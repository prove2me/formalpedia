-- Prove2me | solution 1 for PersistClust.Count.alg_numclust_eq_barcode_forward
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-10T05:05:45.161005+00:00
-- url     : https://prove2.me/submissions/527953a1-1b8c-4a16-bb35-c31a40218429

import Mathlib
import Definitions.Def_PersistClust_Count_Algorithm
import Definitions.Def_PersistClust_Count_AlgBarcode

open PersistClust.Count

/-!
# Forward direction: clusters inject into barcode copies (prominence ≥ τ, birth ≥ τ)

Every cluster output by the `τ`-thresholded union-find Procedure 1 is realized by a
distinct barcode copy of the elder-rule pairing with prominence at least `τ` and
birth at least `τ`.  Sending a surviving root `r` to `(barPair r, rank r)` — its
recorded barcode point under the private per-root death map of the plain sweep,
tagged with its rank among the roots sharing the same point — yields an injection
into the region copy set, hence `numClusters ≤ encard`.

Roadmap (each step is a private lemma below; all currently `sorry`):

* `(BD)` `numclust_fwd_BD_*`: PRIVATE per-root death map of the plain (τ = +∞)
  elder-rule sweep, mirroring `barStep` but recording, for every dying root `r`,
  its death level `g i` instead of accumulating pair multiplicities; `ripsBarcode`
  is identified with the number of roots realizing the point.
* `(R)` `numclust_fwd_R_char`: per-root characterization of the final τ-roots
  counted by `numClusters`: a peak `r` with `τ ≤ g r` survives iff it is immortal
  in the plain sweep (`barDeath r = ⊥`) or it died a strict death with
  prominence `g r - barDeath r ≥ τ`.
* `(I)` `numclust_fwd_I_map_region`: the injection construction
  `r ↦ (barPair r, rank r)` from the root Finset into the region copy set.
* `(M)` `numclust_fwd_M_region` / `numclust_fwd_M_rank`: region membership
  (`barDeath r ≤ g r - τ ∧ τ ≤ g r`) and rank-below-multiplicity
  (`rank r < ripsBarcode (barPair r)`).
* `(J)` `numclust_fwd_J_inj`: injectivity of `r ↦ (barPair r, rank r)` on the
  root Finset.
* `(A)` `numclust_fwd_A_numclust_card` / `numclust_fwd_A_card_le`: the
  encard/card assembly `numClusters = F.card ≤ region.encard`.
-/

noncomputable section

/-- One step of the private per-root death sweep: mirrors `barStep` exactly (same
union-find state evolution) but records for each dying root `r` its death level
`g i` (strict deaths only, as in `barStep`'s dropped-diagonal convention). -/
private def numclust_fwd_deathStep (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (st : UFState n × (Fin n → EReal)) (i : Fin n)
    : UFState n × (Fin n → EReal) :=
  let lab := st.1
  let dth := st.2
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)
  if S = ∅ then (Function.update lab i (some i), dth)
  else
    let root : Fin n → Fin n := fun j => (lab j).getD j
    let ri := root (firstProcessed σ S i)
    let M : Finset (Fin n) := insert ri (S.image root)
    let R := firstProcessed σ M ri
    let lab2 : UFState n := fun v =>
      if v = i then some R
      else match lab v with
        | some r => if r ∈ M then some R else some r
        | none => none
    let dying : Finset (Fin n) :=
      (M.erase R).filter (fun r => (g i : EReal) < (g r : EReal))
    (lab2, fun r => if r ∈ dying then (g i : EReal) else dth r)

/-- The full private death sweep: same fold as `barRun`, from the empty state with
all deaths initialized to `⊥` (immortal / not-yet-dead). -/
private def numclust_fwd_deathRun (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) : UFState n × (Fin n → EReal) :=
  (List.finRange n).reverse.foldl
    (fun st k => numclust_fwd_deathStep n g Dm δ σ st (σ k))
    ((fun _ => none), (fun _ => ⊥))

/-- PRIVATE per-root death map of the plain elder-rule sweep: `numclust_fwd_barDeath r = ⊥`
for immortal (and never-root / tie-absorbed) vertices, and the level `g i` at which
the entry rooted at `r` was merged away, when it died a strict (off-diagonal) death. -/
private def numclust_fwd_barDeath (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (r : Fin n) : EReal :=
  (numclust_fwd_deathRun n g Dm δ σ).2 r

/-- The barcode point realized by root `r` under the private death map. -/
private def numclust_fwd_barPair (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (r : Fin n) : EReal × EReal :=
  ((g r : EReal), numclust_fwd_barDeath n g Dm δ σ r)

/-- The final τ-roots counted by `numClusters`: the fixed points of the final
τ-sweep labeling whose value is at least `τ`. -/
private def numclust_fwd_rootFinset (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun r => ufRun g Dm δ τ σ r = some r ∧ τ ≤ g r)

/-- The rank of `r` among the final τ-roots sharing its barcode point: the number of
such roots strictly below `r` (in the natural order on `Fin n`). -/
private def numclust_fwd_rank (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (r : Fin n) : ℕ :=
  ((numclust_fwd_rootFinset n g Dm δ τ σ).filter
    (fun s => numclust_fwd_barPair n g Dm δ σ s = numclust_fwd_barPair n g Dm δ σ r ∧ s < r)).card

/-- The injection: a final τ-root maps to its barcode copy, tagged by its rank. -/
private def numclust_fwd_map (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (r : Fin n) : (EReal × EReal) × ℕ :=
  (numclust_fwd_barPair n g Dm δ σ r, numclust_fwd_rank n g Dm δ τ σ r)

/-- The region of barcode copies matched by the forward inequality. -/
private def numclust_fwd_regionSet (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) : Set ((EReal × EReal) × ℕ) :=
  {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < ripsBarcode g Dm δ σ q.1 ∧
      q.1.2 ≤ q.1.1 - (τ : EReal) ∧ (τ : EReal) ≤ q.1.1}

/-! #### Named pieces of the merge step (definitional to the inline `let`s of the sweeps) -/

/-- The upper-star neighbour set of `i` under the pre-step label map. -/
private def numclust_fwd_S {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (lab : UFState n)
    (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)

/-- Entry roots in the pre-step labelling: the value of `lab j` when defined, else `j`. -/
private def numclust_fwd_root {n : ℕ} (lab : UFState n) : Fin n → Fin n :=
  fun j => (lab j).getD j

/-- The neighbouring roots merged at the step processing `i`. -/
private def numclust_fwd_M {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (lab : UFState n) (i : Fin n) : Finset (Fin n) :=
  insert (numclust_fwd_root lab (firstProcessed σ (numclust_fwd_S Dm δ lab i) i))
    ((numclust_fwd_S Dm δ lab i).image (numclust_fwd_root lab))

/-- The surviving root of the merge at the step processing `i`. -/
private def numclust_fwd_R {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (lab : UFState n) (i : Fin n) : Fin n :=
  firstProcessed σ (numclust_fwd_M Dm δ σ lab i)
    (numclust_fwd_root lab (firstProcessed σ (numclust_fwd_S Dm δ lab i) i))

/-- The roots dying a strict death at the step processing `i`. -/
private def numclust_fwd_dying {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (lab : UFState n) (i : Fin n) : Finset (Fin n) :=
  ((numclust_fwd_M Dm δ σ lab i).erase (numclust_fwd_R Dm δ σ lab i)).filter
    (fun r => (g i : EReal) < (g r : EReal))

/-- The label part of one private-death step equals that of `barStep` (merge branch). -/
private theorem numclust_fwd_step_fst_ne (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (lab : UFState n) (dth : Fin n → EReal) (acc : (EReal × EReal) → ℕ∞)
    (i : Fin n)
    (hS : (Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)
      : Finset (Fin n)) ≠ ∅) :
    (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1
      = (barStep g Dm δ σ (lab, acc) i).1 := by
  simp only [numclust_fwd_deathStep, barStep, if_neg hS]
  rfl

/-- The label part of one private-death step equals that of `barStep` (peak branch). -/
private theorem numclust_fwd_step_fst_emp (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (lab : UFState n) (dth : Fin n → EReal)
    (acc : (EReal × EReal) → ℕ∞) (i : Fin n)
    (hS : (Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)
      : Finset (Fin n)) = ∅) :
    (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1
      = (barStep g Dm δ σ (lab, acc) i).1 := by
  simp only [numclust_fwd_deathStep, barStep, if_pos hS]

/-- The death map of one private-death step: unchanged on the peak branch, more
precisely `dth` with the dying roots re-valued at `g i` on the merge branch. -/
private theorem numclust_fwd_deathStep_snd (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (lab : UFState n) (dth : Fin n → EReal) (i : Fin n) :
    (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).2 =
      (if Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome) = ∅ then dth
        else fun r => if r ∈ numclust_fwd_dying g Dm δ σ lab i
          then ((g i : EReal)) else dth r) := by
  by_cases hS : (Finset.univ.filter
      (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome) : Finset (Fin n)) = ∅
  · simp only [numclust_fwd_deathStep, if_pos hS]
  · simp only [numclust_fwd_deathStep, if_neg hS]
    rfl

/-- The `barStep` accumulator evolution (both branches, named pieces). -/
private theorem numclust_fwd_barStep_snd (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (lab : UFState n) (acc : (EReal × EReal) → ℕ∞) (i : Fin n)
    (q : EReal × EReal) :
    (barStep g Dm δ σ (lab, acc) i).2 q =
      (if Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome) = ∅ then acc q
        else acc q + (numclust_fwd_dying g Dm δ σ lab i).sum
          (fun r => if q = ((g r : EReal), (g i : EReal)) then (1 : ℕ∞) else 0)) := by
  by_cases hS : (Finset.univ.filter
      (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome) : Finset (Fin n)) = ∅
  · simp only [barStep, if_pos hS]
  · simp only [barStep, if_neg hS]
    rfl

/-! ### (BD) basic lemmas about the private death map -/

/-! ### (BD) reusable machinery for the coupled `barStep`/`deathStep` fold -/

/-- `firstProcessed` returns a member of its (nonempty) set. -/
private theorem numclust_fwd_fp_mem (n : ℕ) (σ : Fin n ≃ Fin n)
    (S : Finset (Fin n)) (i₀ : Fin n) (h : S.Nonempty) : firstProcessed σ S i₀ ∈ S := by
  simp only [firstProcessed, dif_pos h]
  obtain ⟨s, hs, hsx⟩ :=
    Finset.mem_image.mp (Finset.max'_mem (S.image σ.symm) (h.image σ.symm))
  rw [← hsx, σ.apply_symm_apply]; exact hs

/-- `firstProcessed σ S i₀` is the σ-eldest (max-`σ.symm`) member of `S`.
Ported from the reverse lane (needed for the redirect/elder comparisons). -/
private theorem numclust_fwd_firstProcessed_le {n : ℕ} (σ : Fin n ≃ Fin n)
    (S : Finset (Fin n)) (i₀ : Fin n) (hS : S.Nonempty) (x : Fin n) (hx : x ∈ S) :
    (σ.symm x : ℕ) ≤ (σ.symm (firstProcessed σ S i₀) : ℕ) := by
  have hle1 : σ.symm x ≤ (S.image σ.symm).max' (hS.image _) :=
    Finset.le_max' _ _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  rw [Fin.le_iff_val_le_val] at hle1
  have hexp : firstProcessed σ S i₀ = σ ((S.image σ.symm).max' (hS.image _)) := by
    rw [firstProcessed]; rw [dif_pos hS]
  rw [hexp]
  rw [Equiv.symm_apply_apply]
  exact hle1

/-- Re-pointing the entries rooted in `M` to `R` preserves rootedness. -/
private theorem numclust_fwd_lab2_rooted (n : ℕ) (M : Finset (Fin n)) (R i : Fin n)
    (lab : UFState n) (hM : ∀ m ∈ M, lab m = some m) (hRm : R ∈ M) (hni : lab i = none)
    (hR : ∀ v r, lab v = some r → lab r = some r) :
    ∀ x y, (fun v => if v = i then some R else
        match lab v with
        | some r => if r ∈ M then some R else some r
        | none => none) x = some y →
      (fun v => if v = i then some R else
        match lab v with
        | some r => if r ∈ M then some R else some r
        | none => none) y = some y := by
  intros x y hxy
  dsimp only [] at hxy
  by_cases hxi : x = i
  · rw [if_pos hxi] at hxy
    have hEq : R = y := Option.some_inj.mp hxy
    rw [← hEq]
    dsimp only []
    by_cases hRi : R = i
    · rw [if_pos hRi]
    · rw [if_neg hRi, hM R hRm]; dsimp only []; rw [if_pos hRm]
  · rw [if_neg hxi] at hxy
    cases hx : lab x with
    | none => simp [hx] at hxy
    | some r =>
      rw [hx] at hxy
      dsimp only [] at hxy
      by_cases hrm : r ∈ M
      · rw [if_pos hrm] at hxy
        have hEq : R = y := Option.some_inj.mp hxy
        rw [← hEq]
        dsimp only []
        by_cases hRi : R = i
        · rw [if_pos hRi]
        · rw [if_neg hRi, hM R hRm]; dsimp only []; rw [if_pos hRm]
      · rw [if_neg hrm] at hxy
        have hEq : r = y := Option.some_inj.mp hxy
        rw [← hEq]
        dsimp only []
        have hri : r ≠ i := by
          intro hri'
          have h1 : lab i = some r := by rw [← hri']; exact hR x r hx
          rw [hni] at h1
          exact absurd h1 (by simp)
        rw [if_neg hri, hR x r hx]
        show (if r ∈ M then some R else some r) = some r
        rw [if_neg hrm]

/-- Re-pointing entries keeps a fresh vertex unlabelled. -/
private theorem numclust_fwd_lab2_none (n : ℕ) (M : Finset (Fin n)) (R i v : Fin n)
    (lab : UFState n) (hvi : v ≠ i) (hv : lab v = none) :
    (fun w => if w = i then some R else
        match lab w with
        | some r => if r ∈ M then some R else some r
        | none => none) v = none := by
  simp only [if_neg hvi, hv]

/-- A `barStep` preserves rootedness of the label map, given the processed vertex is
fresh.  (The `τ = ∞` merge has no second `E`-merge, so this is the plain `lab2` step.) -/
private theorem numclust_fwd_barStep_rooted (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (lab : UFState n) (acc : EReal × EReal → ℕ∞) (i : Fin n)
    (hR : ∀ v r, lab v = some r → lab r = some r) (hni : lab i = none) :
    ∀ v r, (barStep g Dm δ σ (lab, acc) i).1 v = some r →
           (barStep g Dm δ σ (lab, acc) i).1 r = some r := by
  intros v r hr
  simp only [barStep] at hr ⊢
  let S : Finset (Fin n) := Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)
  let root : Fin n → Fin n := fun j => (lab j).getD j
  let ri : Fin n := root (firstProcessed σ S i)
  let M : Finset (Fin n) := insert ri (S.image root)
  let R : Fin n := firstProcessed σ M ri
  let lab2 : UFState n := fun w => if w = i then some R else
    match lab w with
    | some r => if r ∈ M then some R else some r
    | none => none
  split_ifs with hS
  · rw [if_pos hS] at hr
    dsimp only [] at hr ⊢
    by_cases hvi : v = i
    · rw [hvi] at hr
      rw [Function.update_self] at hr
      rw [← Option.some_inj.mp hr]
      rw [Function.update_self]
    · rw [Function.update_of_ne hvi (some i) lab] at hr
      have hvr : lab r = some r := hR v r hr
      by_cases hri : r = i
      · subst hri; exact absurd (hni.symm.trans hvr) (by simp)
      · rw [Function.update_of_ne hri (some i) lab]; exact hvr
  · rw [if_neg hS] at hr
    have hSne : S.Nonempty := Finset.nonempty_of_ne_empty hS
    have hroot_mem : ∀ j ∈ S, lab ((lab j).getD j) = some ((lab j).getD j) := by
      intros j hj
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hj).2.2.2
      rw [ha]; exact hR j a ha
    have hMroot : ∀ m ∈ M, lab m = some m := by
      intros m hm
      rcases Finset.mem_insert.mp hm with hm' | hm'
      · rw [hm']; exact hroot_mem (firstProcessed σ S i) (numclust_fwd_fp_mem n σ S i hSne)
      · obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp hm'
        rw [← hjm]; exact hroot_mem j hjS
    have hMne : M.Nonempty := ⟨ri, Finset.mem_insert_self _ _⟩
    have hRm : R ∈ M := numclust_fwd_fp_mem n σ M ri hMne
    exact numclust_fwd_lab2_rooted n M R i lab hMroot hRm hni hR v r hr

/-- A `barStep` never newly labels a vertex other than the processed one. -/
private theorem numclust_fwd_barStep_none (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (lab : UFState n) (acc : EReal × EReal → ℕ∞) (i v : Fin n)
    (hv : lab v = none) (hvi : v ≠ i) :
    (barStep g Dm δ σ (lab, acc) i).1 v = none := by
  simp only [barStep]
  let S : Finset (Fin n) := Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)
  let root : Fin n → Fin n := fun j => (lab j).getD j
  let ri : Fin n := root (firstProcessed σ S i)
  let M : Finset (Fin n) := insert ri (S.image root)
  let R : Fin n := firstProcessed σ M ri
  let lab2 : UFState n := fun w => if w = i then some R else
    match lab w with
    | some r => if r ∈ M then some R else some r
    | none => none
  split_ifs with hS
  · dsimp only []
    rw [Function.update_of_ne hvi (some i) lab]; exact hv
  · exact numclust_fwd_lab2_none n M R i v lab hvi hv
/-- Folding `barStep` preserves rootedness of the label map (`σ` injective). -/
private theorem numclust_fwd_barStep_rooted_fold (n : ℕ) (g : Fin n → ℝ)
    (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (σ : Fin n ≃ Fin n) :
    ∀ (l : List (Fin n)) (lab : UFState n) (acc : EReal × EReal → ℕ∞),
      (∀ v r, lab v = some r → lab r = some r) →
      (∀ k ∈ l, lab (σ k) = none) →
      l.Nodup →
      (∀ v r, (l.foldl (fun st k => barStep g Dm δ σ st (σ k)) (lab, acc)).1 v = some r →
              (l.foldl (fun st k => barStep g Dm δ σ st (σ k)) (lab, acc)).1 r = some r) := by
  intro l
  induction l with
  | nil => intro lab acc hR _ _; simpa only [List.foldl_nil] using hR
  | cons k ks ih =>
    intros lab acc hR hFresh hND
    obtain ⟨hND', hNDks⟩ := List.nodup_cons.mp hND
    have hFreshK : lab (σ k) = none := hFresh k List.mem_cons_self
    have hR1 := numclust_fwd_barStep_rooted n g Dm δ σ lab acc (σ k) hR hFreshK
    have hFresh1 : ∀ j ∈ ks, (barStep g Dm δ σ (lab, acc) (σ k)).1 (σ j) = none := by
      intros j hj
      apply numclust_fwd_barStep_none n g Dm δ σ lab acc (σ k) (σ j)
        (hFresh j (List.mem_cons_of_mem _ hj))
      intro heq
      exact absurd (Equiv.injective σ heq) (fun (h : j = k) => hND' (h ▸ hj))
    rw [List.foldl_cons]
    exact ih (barStep g Dm δ σ (lab, acc) (σ k)).1 (barStep g Dm δ σ (lab, acc) (σ k)).2
      hR1 hFresh1 hNDks

/-- Off-diagonal barcode multiplicity equals the number of roots dying a strict
(off-diagonal) death at that point. -/
private theorem numclust_fwd_BD_barcode_real (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) :
    ∀ p : EReal × EReal, p.2 ≠ ⊥ →
      ripsBarcode g Dm δ σ p
        = ((Finset.univ.filter
              (fun r => numclust_fwd_barPair n g Dm δ σ r = p)).card : ℕ∞) := by
  intro p hp
  -- Immortal bars never contribute at a point whose death coordinate is not `⊥`.
  have hsum0 : (Finset.univ.filter (fun r => (barRun g Dm δ σ).1 r = some r)).sum
      (fun r => if p = ((g r : EReal), (⊥ : EReal)) then (1 : ℕ∞) else 0) = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => by split_ifs <;> simp)).mpr
    intro r _
    exact if_neg (fun heq => hp (congrArg Prod.snd heq))
  -- One merge step adds to the accumulator exactly the dying roots' new fibre.
  have key : ∀ (D : Finset (Fin n)) (dth : Fin n → EReal) (acc : (EReal × EReal) → ℕ∞)
      (i : Fin n) (q : EReal × EReal),
      (∀ r ∈ D, dth r = ⊥) → q.2 ≠ ⊥ →
      acc q = ((Finset.univ.filter (fun r => ((g r : EReal), dth r) = q)).card : ℕ∞) →
      acc q + D.sum (fun r => if q = ((g r : EReal), (g i : EReal)) then (1 : ℕ∞) else 0)
        = ((Finset.univ.filter (fun r => ((g r : EReal),
            (if r ∈ D then ((g i : EReal)) else dth r)) = q)).card : ℕ∞) := by
    intro D dth acc i q hDdth hq hacc
    have hpart : Finset.univ.filter (fun r => ((g r : EReal),
          (if r ∈ D then ((g i : EReal)) else dth r)) = q)
        = (Finset.univ.filter (fun r => ((g r : EReal), dth r) = q)) ∪
          (D.filter (fun r => q = ((g r : EReal), (g i : EReal)))) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      by_cases hrD : r ∈ D
      · rw [if_pos hrD]
        constructor
        · intro h; exact Or.inr ⟨hrD, h.symm⟩
        · rintro (h1 | ⟨_, h2⟩)
          · exact absurd ((congrArg Prod.snd h1).symm.trans (hDdth r hrD)) hq
          · exact h2.symm
      · rw [if_neg hrD]
        constructor
        · intro h; exact Or.inl h
        · rintro (h1 | ⟨h2, _⟩)
          · exact h1
          · exact absurd h2 hrD
    have hdisj : Disjoint (Finset.univ.filter (fun r => ((g r : EReal), dth r) = q))
        (D.filter (fun r => q = ((g r : EReal), (g i : EReal)))) := by
      rw [Finset.disjoint_left]
      intro r hrO hrD
      exact hq ((congrArg Prod.snd (Finset.mem_filter.mp hrO).2).symm.trans
        (hDdth r (Finset.mem_filter.mp hrD).1))
    have hsumD : D.sum (fun r => if q = ((g r : EReal), (g i : EReal)) then (1 : ℕ∞) else 0)
        = ((D.filter (fun r => q = ((g r : EReal), (g i : EReal)))).card : ℕ∞) := by
      rw [← Finset.sum_filter, Finset.sum_const, Nat.smul_one_eq_cast]
    rw [hpart, Finset.card_union_of_disjoint hdisj, Nat.cast_add, hacc, hsumD]
  -- Coupled fold induction: the `barStep` accumulator tracks the recorded deaths.
  have hcore : ∀ (l : List (Fin n)), l.Nodup →
      ∀ (s1 : UFState n × (Fin n → EReal)) (s2 : UFState n × ((EReal × EReal) → ℕ∞)),
      s1.1 = s2.1 →
      (∀ k ∈ l, s1.1 (σ k) = none ∧ s1.2 (σ k) = ⊥) →
      (∀ v r, s1.1 v = some r → s1.1 r = some r) →
      (∀ v r, s1.1 v = some r → s1.2 r = ⊥) →
      (∀ q, q.2 ≠ ⊥ → s2.2 q =
        ((Finset.univ.filter (fun r => ((g r : EReal), s1.2 r) = q)).card : ℕ∞)) →
      (l.foldl (fun st k => barStep g Dm δ σ st (σ k)) s2).2 p =
        ((Finset.univ.filter (fun r => ((g r : EReal),
          (l.foldl (fun st k => numclust_fwd_deathStep n g Dm δ σ st (σ k)) s1).2 r) = p)).card : ℕ∞) := by
    intro l
    induction l with
    | nil =>
      intro _ s1 s2 _ _ _ _ hC
      rw [List.foldl_nil, List.foldl_nil]
      exact hC p hp
    | cons k ks ih =>
      intro hnd s1 s2 hlab hfresh hroot hp2 hC
      obtain ⟨hkd, hksnd⟩ := List.nodup_cons.mp hnd
      obtain ⟨lab, dth⟩ := s1
      obtain ⟨lab₂, acc⟩ := s2
      have hlab' : lab = lab₂ := hlab
      subst hlab'
      simp only [Prod.fst, Prod.snd] at hfresh hroot hp2 hC
      simp only [List.foldl_cons]
      by_cases hS : (Finset.univ.filter
          (fun j => j ≠ (σ k) ∧ Dm (σ k) j ≤ δ ∧ (lab j).isSome) : Finset (Fin n)) = ∅
      · -- peak branch: no merge, the state is only relabelled at the fresh vertex
        have hb : (numclust_fwd_deathStep n g Dm δ σ (lab, dth) (σ k)).1
            = (barStep g Dm δ σ (lab, acc) (σ k)).1 :=
          numclust_fwd_step_fst_emp n g Dm δ σ lab dth acc (σ k) hS
        refine ih hksnd _ _ hb ?_ ?_ ?_ ?_
        · intro j hj
          refine ⟨?_, ?_⟩
          · rw [hb]
            exact numclust_fwd_barStep_none n g Dm δ σ lab acc (σ k) (σ j)
              (hfresh j (List.mem_cons_of_mem _ hj)).1
              (fun heq => hkd ((Equiv.injective σ heq).symm ▸ hj))
          · rw [numclust_fwd_deathStep_snd n g Dm δ σ lab dth (σ k), if_pos hS]
            exact (hfresh j (List.mem_cons_of_mem _ hj)).2
        · rw [hb]
          exact numclust_fwd_barStep_rooted n g Dm δ σ lab acc (σ k) hroot
            (hfresh k List.mem_cons_self).1
        · intro v r hlr
          simp only [numclust_fwd_deathStep, if_pos hS] at hlr
          by_cases hv : v = (σ k)
          · rw [hv, Function.update_self] at hlr
            rw [numclust_fwd_deathStep_snd n g Dm δ σ lab dth (σ k), if_pos hS]
            rw [(Option.some_inj.mp hlr).symm]
            exact (hfresh k List.mem_cons_self).2
          · rw [Function.update_of_ne hv (some (σ k)) lab] at hlr
            rw [numclust_fwd_deathStep_snd n g Dm δ σ lab dth (σ k), if_pos hS]
            exact hp2 v r hlr
        · intro q hq
          rw [numclust_fwd_barStep_snd n g Dm δ σ lab acc (σ k) q, if_pos hS,
              numclust_fwd_deathStep_snd n g Dm δ σ lab dth (σ k), if_pos hS]
          exact hC q hq
      · -- merge branch
        have hb : (numclust_fwd_deathStep n g Dm δ σ (lab, dth) (σ k)).1
            = (barStep g Dm δ σ (lab, acc) (σ k)).1 :=
          numclust_fwd_step_fst_ne n g Dm δ σ lab dth acc (σ k) hS
        have hsub : ∀ j ∈ numclust_fwd_S Dm δ lab (σ k), (lab j).isSome :=
          fun j hj => (Finset.mem_filter.mp hj).2.2.2
        have hMroot : ∀ m ∈ numclust_fwd_M Dm δ σ lab (σ k), lab m = some m := by
          intro m hm
          rcases Finset.mem_insert.mp hm with hm' | hm'
          · rw [hm']
            obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp
              (hsub _ (numclust_fwd_fp_mem n σ _ (σ k) (Finset.nonempty_of_ne_empty hS)))
            simp only [numclust_fwd_root]
            rw [ha]
            exact hroot _ _ ha
          · obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp hm'
            obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hsub j hjS)
            rw [← hjm]
            simp only [numclust_fwd_root]
            rw [ha]
            exact hroot _ _ ha
        have hRmem : numclust_fwd_R Dm δ σ lab (σ k) ∈ numclust_fwd_M Dm δ σ lab (σ k) :=
          numclust_fwd_fp_mem n σ _
            (numclust_fwd_root lab (firstProcessed σ (numclust_fwd_S Dm δ lab (σ k)) (σ k)))
            (Finset.insert_nonempty _ _)
        have hDdth : ∀ r ∈ numclust_fwd_dying g Dm δ σ lab (σ k), dth r = ⊥ := by
          intro r hr
          obtain ⟨hrE, _⟩ := Finset.mem_filter.mp hr
          exact hp2 r r (hMroot r (Finset.mem_of_mem_erase hrE))
        have hC' : ∀ q, q.2 ≠ ⊥ → (barStep g Dm δ σ (lab, acc) (σ k)).2 q =
            ((Finset.univ.filter (fun r => ((g r : EReal),
              (numclust_fwd_deathStep n g Dm δ σ (lab, dth) (σ k)).2 r) = q)).card : ℕ∞) := by
          intro q hq
          rw [numclust_fwd_barStep_snd n g Dm δ σ lab acc (σ k) q, if_neg hS,
              numclust_fwd_deathStep_snd n g Dm δ σ lab dth (σ k), if_neg hS]
          exact key (numclust_fwd_dying g Dm δ σ lab (σ k)) dth acc (σ k) q hDdth hq (hC q hq)
        refine ih hksnd _ _ hb ?_ ?_ ?_ hC'
        · intro j hj
          refine ⟨?_, ?_⟩
          · rw [hb]
            exact numclust_fwd_barStep_none n g Dm δ σ lab acc (σ k) (σ j)
              (hfresh j (List.mem_cons_of_mem _ hj)).1
              (fun heq => hkd ((Equiv.injective σ heq).symm ▸ hj))
          · rw [numclust_fwd_deathStep_snd n g Dm δ σ lab dth (σ k), if_neg hS]
            have hvnot : ¬((σ j) ∈ numclust_fwd_dying g Dm δ σ lab (σ k)) := by
              intro hd
              simp only [numclust_fwd_dying, Finset.mem_filter] at hd
              exact absurd (hMroot (σ j) (Finset.mem_of_mem_erase hd.1))
                (by rw [(hfresh j (List.mem_cons_of_mem _ hj)).1]; simp)
            rw [if_neg hvnot]
            exact (hfresh j (List.mem_cons_of_mem _ hj)).2
        · rw [hb]
          exact numclust_fwd_barStep_rooted n g Dm δ σ lab acc (σ k) hroot
            (hfresh k List.mem_cons_self).1
        · intro v r hlr
          have hcase : r = numclust_fwd_R Dm δ σ lab (σ k) ∨
              ∃ r', r' ∉ numclust_fwd_M Dm δ σ lab (σ k) ∧ lab v = some r' ∧ r = r' := by
            simp only [numclust_fwd_deathStep, if_neg hS] at hlr
            by_cases hv : v = (σ k)
            · rw [hv, if_pos rfl] at hlr
              exact Or.inl (Option.some_inj.mp hlr).symm
            · rw [if_neg hv] at hlr
              cases hlv : lab v with
              | none => rw [hlv] at hlr; simp at hlr
              | some r' =>
                simp only [hlv] at hlr
                split_ifs at hlr with hrM
                · exact Or.inl (Option.some_inj.mp hlr).symm
                · exact Or.inr ⟨r', hrM, rfl, (Option.some_inj.mp hlr).symm⟩
          rcases hcase with hR | ⟨r', hr'M, hlv, hr'r⟩
          · have hnotd : ¬((numclust_fwd_R Dm δ σ lab (σ k)) ∈ numclust_fwd_dying g Dm δ σ lab (σ k)) := by
              intro hd
              simp only [numclust_fwd_dying, Finset.mem_filter] at hd
              exact Finset.notMem_erase (numclust_fwd_R Dm δ σ lab (σ k))
                (numclust_fwd_M Dm δ σ lab (σ k)) hd.1
            rw [hR, numclust_fwd_deathStep_snd n g Dm δ σ lab dth (σ k), if_neg hS, if_neg hnotd]
            exact hp2 (numclust_fwd_R Dm δ σ lab (σ k)) (numclust_fwd_R Dm δ σ lab (σ k))
              (hMroot (numclust_fwd_R Dm δ σ lab (σ k)) hRmem)
          · have hnotd : ¬(r ∈ numclust_fwd_dying g Dm δ σ lab (σ k)) := by
              intro hd
              simp only [numclust_fwd_dying, Finset.mem_filter] at hd
              exact hr'M (by rw [← hr'r]; exact Finset.mem_of_mem_erase hd.1)
            rw [numclust_fwd_deathStep_snd n g Dm δ σ lab dth (σ k), if_neg hS, if_neg hnotd, hr'r]
            exact hp2 v r' hlv
  -- Assemble: `ripsBarcode = acc + immortals`, with both parts identified.
  unfold ripsBarcode
  rw [hsum0, add_zero]
  have hnodup : (List.finRange n).reverse.Nodup := (List.nodup_reverse).mpr (List.nodup_finRange n)
  have hind := hcore (List.finRange n).reverse hnodup
    ((fun _ => none), (fun _ => (⊥ : EReal))) ((fun _ => none), (fun _ => (0 : ℕ∞))) rfl
    (fun k _ => ⟨rfl, rfl⟩)
    (fun v r h => absurd h (by simp))
    (fun v r h => absurd h (by simp))
    (fun q hq => by
      have hempty : Finset.univ.filter
          (fun r => ((g r : EReal), (fun _ => (⊥ : EReal)) r) = q) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro r _ hmem
        exact hq (by simpa using (congrArg Prod.snd hmem).symm)
      simp only [hempty, Finset.card_empty, Nat.cast_zero])
  simp only [barRun, numclust_fwd_barPair, numclust_fwd_barDeath, numclust_fwd_deathRun]
  exact hind

/-- Immortal barcode multiplicity equals the number of immortal roots at that birth
level. -/
private theorem numclust_fwd_BD_barcode_immortal (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) :
    ∀ b : EReal,
      ripsBarcode g Dm δ σ (b, ⊥)
        = ((Finset.univ.filter
              (fun r => (barRun g Dm δ σ).1 r = some r ∧ (g r : EReal) = b)).card : ℕ∞) := by
  intro b
  -- The accumulated pairs never have a `⊥` death coordinate, since every recorded
  -- death is the (real) level `g i` of a processed vertex.
  have A0 : ∀ p : EReal × EReal, p.2 = ⊥ → (barRun g Dm δ σ).2 p = (0 : ℕ∞) := by
    intro p hp
    have step : ∀ (s : UFState n × ((EReal × EReal) → ℕ∞)) (k : Fin n),
        s.2 p = 0 → (barStep g Dm δ σ s (σ k)).2 p = 0 := by
      intro s k h0
      by_cases hS : (Finset.univ.filter
          (fun j => j ≠ (σ k) ∧ Dm (σ k) j ≤ δ ∧ (s.1 j).isSome) : Finset (Fin n)) = ∅
      · simp only [barStep, if_pos hS]
        exact h0
      · simp only [barStep, if_neg hS]
        rw [h0, zero_add]
        apply (Finset.sum_eq_zero_iff_of_nonneg
          (fun r _ => by split_ifs <;> simp)).mpr
        intro r _
        by_cases hpe : p = ((g r : EReal), (g (σ k) : EReal))
        · exact absurd ((congrArg Prod.snd hpe).symm.trans hp) (EReal.coe_ne_bot (g (σ k)))
        · exact if_neg hpe
    have fold : ∀ (l : List (Fin n)) (s : UFState n × ((EReal × EReal) → ℕ∞)),
        s.2 p = 0 → (l.foldl (fun st k => barStep g Dm δ σ st (σ k)) s).2 p = 0 := by
      intro l s h0
      induction l generalizing s with
      | nil => simpa only [List.foldl_nil] using h0
      | cons k ks ih =>
        simp only [List.foldl_cons]
        exact ih (barStep g Dm δ σ s (σ k)) (step s k h0)
    simpa only [barRun] using
      fold (List.finRange n).reverse ((fun _ => none), (fun _ => (0 : ℕ∞))) rfl
  -- `ripsBarcode` splits into the accumulator (zero on the bottom line) plus the
  -- immortal count, which is a sum of indicators over the final roots.
  unfold ripsBarcode
  rw [A0 (b, ⊥) rfl, zero_add]
  have key : ∀ r : Fin n, ((b, (⊥ : EReal)) = ((g r : EReal), (⊥ : EReal))) ↔ (g r : EReal) = b := by
    intro r
    simp only [Prod.mk.injEq, and_true]
    exact Eq.comm
  simp only [key]
  rw [← Finset.sum_filter, Finset.filter_filter, Finset.sum_const, Nat.smul_one_eq_cast]

/-- The plain sweep and the private death sweep have identical union-find states:
the two sweeps evolve the label map by textually identical rules; only the second
component (death map vs. pair multiplicity accumulator) differs. -/
private theorem numclust_fwd_BD_states_eq (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) :
    (numclust_fwd_deathRun n g Dm δ σ).1 = (barRun g Dm δ σ).1 := by
  -- One step: the label parts coincide, since both computations are the same
  -- function of the incoming label map (the second state component is ignored).
  have step : ∀ (s1 : UFState n × (Fin n → EReal))
                   (s2 : UFState n × ((EReal × EReal) → ℕ∞)) (i : Fin n),
      s1.1 = s2.1 →
        (numclust_fwd_deathStep n g Dm δ σ s1 i).1 = (barStep g Dm δ σ s2 i).1 := by
    intros s1 s2 i h
    obtain ⟨lab, dth⟩ := s1
    obtain ⟨lab₂, acc⟩ := s2
    have h' : lab = lab₂ := h
    subst h'
    -- both reductions depend only on the (now common) label map; split on `S = ∅`.
    by_cases hS : (Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)
                    : Finset (Fin n)) = ∅
    · simp only [numclust_fwd_deathStep, barStep, if_pos hS]
    · simp only [numclust_fwd_deathStep, barStep, if_neg hS]
      rfl
  -- Fold induction: equal label parts are preserved across the whole sweep.
  have fold : ∀ (l : List (Fin n)) (s1 : UFState n × (Fin n → EReal))
                    (s2 : UFState n × ((EReal × EReal) → ℕ∞)),
      s1.1 = s2.1 →
        (l.foldl (fun st k => numclust_fwd_deathStep n g Dm δ σ st (σ k)) s1).1 =
          (l.foldl (fun st k => barStep g Dm δ σ st (σ k)) s2).1 := by
    intro l s1 s2
    induction l generalizing s1 s2 with
    | nil => intro h; simp only [List.foldl_nil]; exact h
    | cons k ks ih =>
      intro h
      simp only [List.foldl_cons]
      exact ih _ _ (step s1 s2 (σ k) h)
  -- Both sweeps start from the empty label map; only the second component differs.
  simp only [numclust_fwd_deathRun, barRun]
  exact fold (List.finRange n).reverse ((fun _ => none), (fun _ => ⊥))
      ((fun _ => none), (fun _ => 0)) rfl

/-! ### (R0) reusable τ-sweep (`ufStep`) machinery for the characterization -/

/-- Re-pointing the entries rooted at `R` to `E` (the second τ-merge) keeps labels
pointing to fixed points. -/
private theorem numclust_fwd_merge_rooted (n : ℕ) (lab2 : UFState n) (E R : Fin n)
    (hE : lab2 E = some E) (hER : E ≠ R)
    (hroot : ∀ x y, lab2 x = some y → lab2 y = some y) :
    ∀ x y, (fun v => if lab2 v = some R then some E else lab2 v) x = some y →
      (fun v => if lab2 v = some R then some E else lab2 v) y = some y := by
  intros x y hxy
  dsimp only [] at hxy
  by_cases hxR : lab2 x = some R
  · rw [if_pos hxR] at hxy
    have hEq : E = y := Option.some_inj.mp hxy
    rw [← hEq]
    dsimp only []
    rw [if_neg (fun h => hER (Option.some_inj.mp (h.symm.trans hE)).symm)]
    exact hE
  · rw [if_neg hxR] at hxy
    have hy : lab2 y = some y := hroot x y hxy
    by_cases hyR : lab2 y = some R
    · have hEq : y = R := Option.some_inj.mp (hy.symm.trans hyR)
      rw [hEq] at hxy
      exact absurd hxy hxR
    · dsimp only []; rw [if_neg hyR]; exact hy

/-- The second τ-merge keeps an unlabelled vertex unlabelled. -/
private theorem numclust_fwd_merge_none (n : ℕ) (lab2 : UFState n) (E R v : Fin n)
    (hv : lab2 v = none) : (fun w => if lab2 w = some R then some E else lab2 w) v = none := by
  simp [hv]

/-- A τ-sweep step never newly labels a vertex other than the processed one. -/
private theorem numclust_fwd_ufStep_none (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (lab : UFState n) (i v : Fin n)
    (hv : lab v = none) (hvi : v ≠ i) : ufStep g Dm δ τ σ lab i v = none := by
  simp only [ufStep]
  let S : Finset (Fin n) := Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)
  let ri : Fin n := (lab (firstProcessed σ S i)).getD (firstProcessed σ S i)
  let M : Finset (Fin n) :=
    insert ri ((Finset.image (fun j => (lab j).getD j) S).filter (fun r => g r - g i < τ))
  let R : Fin n := firstProcessed σ M ri
  let lab2 : UFState n := fun w => if w = i then some R else
    match lab w with
    | some r => if r ∈ M then some R else some r
    | none => none
  let E : Fin n := firstProcessed σ (Finset.image (fun j => (lab2 j).getD j) S) R
  split_ifs with hS hC
  · rw [Function.update_of_ne hvi (some i) lab]; exact hv
  · exact numclust_fwd_merge_none n lab2 E R v (numclust_fwd_lab2_none n M R i v lab hvi hv)
  · exact numclust_fwd_lab2_none n M R i v lab hvi hv

/-- The second τ-merge (`Rτ → E`) labels a vertex iff the pre-label (`lab2τ`) does. -/
private theorem numclust_fwd_urelabel_isSome {n : ℕ} (lab2 : UFState n) (E R v : Fin n)
    (h : lab2 v = some R) :
    ((fun w => if lab2 w = some R then some E else lab2 w) v : Option (Fin n)).isSome = true := by
  dsimp only []
  rw [if_pos h]
  rfl

private theorem numclust_fwd_urelabel_isSome_iff {n : ℕ} (lab2 : UFState n) (E R v : Fin n) :
    ((fun w => if lab2 w = some R then some E else lab2 w) v : Option (Fin n)).isSome
      = (lab2 v).isSome := by
  dsimp only []
  by_cases h : lab2 v = some R
  · rw [if_pos h, h]; rfl
  · rw [if_neg h]

/-- The τ merge relabelling (`lab2τ`) labels exactly the pre-processed vertices off `i`. -/
private theorem numclust_fwd_ulab2_isSome {n : ℕ} (M : Finset (Fin n)) (R i v : Fin n)
    (lab : UFState n) (hvi : v ≠ i) :
    ((fun w => if w = i then some R else
        match lab w with
        | some r => if r ∈ M then some R else some r
        | none => none) v : Option (Fin n)).isSome = (lab v).isSome := by
  dsimp only []
  rw [if_neg hvi]
  cases lab v with
  | none => rfl
  | some r =>
    dsimp only []
    by_cases hr : r ∈ M
    · rw [if_pos hr]; rfl
    · rw [if_neg hr]

/-- The τ merge relabelling labels the processed vertex `i`. -/
private theorem numclust_fwd_ulab2_self {n : ℕ} (M : Finset (Fin n)) (R i : Fin n)
    (lab : UFState n) :
    ((fun w => if w = i then some R else
        match lab w with
        | some r => if r ∈ M then some R else some r
        | none => none) i : Option (Fin n)).isSome = true := by
  dsimp only []
  rw [if_pos rfl]
  rfl

/-- A τ-sweep step labels the processed vertex `i`. -/
private theorem numclust_fwd_ufStep_isSome_i (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (lab : UFState n) (i : Fin n) :
    (ufStep g Dm δ τ σ lab i i).isSome = true := by
  simp only [ufStep]
  let S : Finset (Fin n) := Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)
  let ri : Fin n := (lab (firstProcessed σ S i)).getD (firstProcessed σ S i)
  let M : Finset (Fin n) :=
    insert ri ((Finset.image (fun j => (lab j).getD j) S).filter (fun r => g r - g i < τ))
  let R : Fin n := firstProcessed σ M ri
  let lab2 : UFState n := fun w => if w = i then some R else
    match lab w with
    | some r => if r ∈ M then some R else some r
    | none => none
  let E : Fin n := firstProcessed σ (Finset.image (fun j => (lab2 j).getD j) S) R
  split_ifs with hS hC
  · rw [Function.update_self]; rfl
  · exact numclust_fwd_urelabel_isSome lab2 E R i (by dsimp only [lab2]; rw [if_pos rfl])
  · exact numclust_fwd_ulab2_self M R i lab

/-- A τ-sweep step never unlabels a vertex other than the processed one. -/
private theorem numclust_fwd_ufStep_isSome (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (lab : UFState n) (i v : Fin n) (hvi : v ≠ i) :
    (ufStep g Dm δ τ σ lab i v).isSome = (lab v).isSome := by
  simp only [ufStep]
  let S : Finset (Fin n) := Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)
  let ri : Fin n := (lab (firstProcessed σ S i)).getD (firstProcessed σ S i)
  let M : Finset (Fin n) :=
    insert ri ((Finset.image (fun j => (lab j).getD j) S).filter (fun r => g r - g i < τ))
  let R : Fin n := firstProcessed σ M ri
  let lab2 : UFState n := fun w => if w = i then some R else
    match lab w with
    | some r => if r ∈ M then some R else some r
    | none => none
  let E : Fin n := firstProcessed σ (Finset.image (fun j => (lab2 j).getD j) S) R
  split_ifs with hS hC
  · rw [Function.update_of_ne hvi (some i) lab]
  · exact (numclust_fwd_urelabel_isSome_iff lab2 E R v).trans
      (numclust_fwd_ulab2_isSome M R i v lab hvi)
  · exact numclust_fwd_ulab2_isSome M R i v lab hvi

/-- A τ-sweep step preserves rootedness of the label map, given the processed vertex
is fresh. -/
private theorem numclust_fwd_ufStep_rooted (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (lab : UFState n) (i : Fin n)
    (hR : ∀ v r, lab v = some r → lab r = some r) (hni : lab i = none) :
    ∀ v r, ufStep g Dm δ τ σ lab i v = some r →
      ufStep g Dm δ τ σ lab i r = some r := by
  intros v r hr
  simp only [ufStep] at hr ⊢
  let S : Finset (Fin n) := Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)
  let ri : Fin n := (lab (firstProcessed σ S i)).getD (firstProcessed σ S i)
  let M : Finset (Fin n) :=
    insert ri ((Finset.image (fun j => (lab j).getD j) S).filter (fun r => g r - g i < τ))
  let R : Fin n := firstProcessed σ M ri
  let lab2 : UFState n := fun w => if w = i then some R else
    match lab w with
    | some r => if r ∈ M then some R else some r
    | none => none
  let E : Fin n := firstProcessed σ (Finset.image (fun j => (lab2 j).getD j) S) R
  split_ifs with hS hC
  · -- i starts a fresh entry rooted at itself.
    rw [if_pos hS] at hr
    by_cases hvi : v = i
    · rw [hvi] at hr
      rw [Function.update_self] at hr
      rw [← Option.some_inj.mp hr]
      rw [Function.update_self]
    · rw [Function.update_of_ne hvi (some i) lab] at hr
      have hvr : lab r = some r := hR v r hr
      by_cases hri : r = i
      · subst hri; exact absurd (hni.symm.trans hvr) (by simp)
      · rw [Function.update_of_ne hri (some i) lab]; exact hvr
  · -- S ≠ ∅, second merge fires: the result is `E`, a lab2-root.
    rw [if_neg hS, if_pos hC] at hr
    have hSne : S.Nonempty := Finset.nonempty_of_ne_empty hS
    have hroot_mem : ∀ j ∈ S, lab ((lab j).getD j) = some ((lab j).getD j) := by
      intros j hj
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hj).2.2.2
      rw [ha]; exact hR j a ha
    have hMroot : ∀ m ∈ M, lab m = some m := by
      intros m hm
      rcases Finset.mem_insert.mp hm with hm' | hm'
      · rw [hm']; exact hroot_mem (firstProcessed σ S i) (numclust_fwd_fp_mem n σ S i hSne)
      · obtain ⟨hm'', _⟩ := Finset.mem_filter.mp hm'
        obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp hm''
        rw [← hjm]; exact hroot_mem j hjS
    have hMne : M.Nonempty := ⟨ri, Finset.mem_insert_self _ _⟩
    have hRm : R ∈ M := numclust_fwd_fp_mem n σ M ri hMne
    have hlab2rooted : ∀ x y, lab2 x = some y → lab2 y = some y :=
      numclust_fwd_lab2_rooted n M R i lab hMroot hRm hni hR
    have hEroot : lab2 E = some E := by
      have hSne2 : (Finset.image (fun j => (lab2 j).getD j) S).Nonempty := by
        obtain ⟨j, hj⟩ := hSne
        exact ⟨(lab2 j).getD j, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
      have hEin : E ∈ Finset.image (fun j => (lab2 j).getD j) S :=
        numclust_fwd_fp_mem n σ _ _ hSne2
      obtain ⟨j, hjS, hjE⟩ := Finset.mem_image.mp hEin
      have hisj : (lab2 j).isSome := by
        have h1 : j ≠ i := (Finset.mem_filter.mp hjS).2.1
        have h2 : (lab j).isSome := (Finset.mem_filter.mp hjS).2.2.2
        show ((if j = i then some R else
          match lab j with
          | some r => if r ∈ M then some R else some r
          | none => none)).isSome
        rw [if_neg h1]
        cases hlab2j : lab j with
        | none => rw [hlab2j] at h2; simp at h2
        | some a => dsimp only []; split <;> exact Option.isSome_some
      have hlab2jE : lab2 j = some E := by
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hisj
        have hget : (lab2 j).getD j = a := by rw [ha]; rfl
        have hAE : a = E := hget.symm.trans hjE
        rw [ha, hAE]
      exact hlab2rooted j E hlab2jE
    exact numclust_fwd_merge_rooted n lab2 E R hEroot hC.1 hlab2rooted v r hr
  · -- S ≠ ∅, no second merge: the result is lab2 itself, a rooted map.
    rw [if_neg hS, if_neg hC] at hr
    have hSne : S.Nonempty := Finset.nonempty_of_ne_empty hS
    have hroot_mem : ∀ j ∈ S, lab ((lab j).getD j) = some ((lab j).getD j) := by
      intros j hj
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hj).2.2.2
      rw [ha]; exact hR j a ha
    have hMroot : ∀ m ∈ M, lab m = some m := by
      intros m hm
      rcases Finset.mem_insert.mp hm with hm' | hm'
      · rw [hm']; exact hroot_mem (firstProcessed σ S i) (numclust_fwd_fp_mem n σ S i hSne)
      · obtain ⟨hm'', _⟩ := Finset.mem_filter.mp hm'
        obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp hm''
        rw [← hjm]; exact hroot_mem j hjS
    have hMne : M.Nonempty := ⟨ri, Finset.mem_insert_self _ _⟩
    have hRm : R ∈ M := numclust_fwd_fp_mem n σ M ri hMne
    exact
      numclust_fwd_lab2_rooted n M R i lab hMroot hRm hni hR v r hr

/-- Folding the τ-sweep preserves rootedness of the label map (`σ` injective). -/
private theorem numclust_fwd_ufStep_rooted_fold (n : ℕ) (g : Fin n → ℝ)
    (Dm : Fin n → Fin n → ℝ) (δ τ : ℝ) (σ : Fin n ≃ Fin n) :
    ∀ (l : List (Fin n)) (lab : UFState n),
      (∀ v r, lab v = some r → lab r = some r) →
      (∀ k ∈ l, lab (σ k) = none) →
      l.Nodup →
      (∀ v r, (l.foldl (fun lab k => ufStep g Dm δ τ σ lab (σ k)) lab) v = some r →
              (l.foldl (fun lab k => ufStep g Dm δ τ σ lab (σ k)) lab) r = some r) := by
  intro l
  induction l with
  | nil => intro lab hR; exact fun _ _ => hR
  | cons k ks ih =>
    intros lab hR hFresh hND
    obtain ⟨hND', hNDks⟩ := List.nodup_cons.mp hND
    have hFreshK : lab (σ k) = none := hFresh k List.mem_cons_self
    have hR1 := numclust_fwd_ufStep_rooted n g Dm δ τ σ lab (σ k) hR hFreshK
    have hFresh1 : ∀ j ∈ ks, ufStep g Dm δ τ σ lab (σ k) (σ j) = none := by
      intros j hj
      apply numclust_fwd_ufStep_none n g Dm δ τ σ lab (σ k) (σ j)
        (hFresh j (List.mem_cons_of_mem _ hj))
      intro heq
      exact absurd (Equiv.injective σ heq) (fun (h : j = k) => hND' (h ▸ hj))
    rw [List.foldl_cons]
    exact ih (ufStep g Dm δ τ σ lab (σ k)) hR1 hFresh1 hNDks

/-! ### (R) coupled τ-sweep / plain-death machinery for the root characterization -/

/-- One coupled step: the τ-sweep label map (`ufStep`) evolves together with the
plain-sweep label map and the private death map (both driven by `numclust_fwd_deathStep`,
whose label projection agrees with `barStep` by `numclust_fwd_step_fst_*`). -/
private def numclust_fwd_cstep (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ τ : ℝ)
    (σ : Fin n ≃ Fin n) (st : UFState n × UFState n × (Fin n → EReal)) (i : Fin n) :
    UFState n × UFState n × (Fin n → EReal) :=
  (ufStep g Dm δ τ σ st.1 i,
   (numclust_fwd_deathStep n g Dm δ σ (st.2.1, st.2.2) i).1,
   (numclust_fwd_deathStep n g Dm δ σ (st.2.1, st.2.2) i).2)

/-- The full coupled run, folding `(finRange n).reverse` from the empty τ-label map,
empty plain-label map, and all-deaths-`⊥` map. -/
private def numclust_fwd_cRun (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ τ : ℝ)
    (σ : Fin n ≃ Fin n) : UFState n × UFState n × (Fin n → EReal) :=
  (List.finRange n).reverse.foldl (fun st k => numclust_fwd_cstep n g Dm δ τ σ st (σ k))
    ((fun _ => none), (fun _ => none), (fun _ => ⊥))

private theorem numclust_fwd_cstep_uf {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (st : UFState n × UFState n × (Fin n → EReal))
    (i : Fin n) :
    (numclust_fwd_cstep n g Dm δ τ σ st i).1 = ufStep g Dm δ τ σ st.1 i := rfl

private theorem numclust_fwd_cstep_lab {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (st : UFState n × UFState n × (Fin n → EReal))
    (i : Fin n) :
    (numclust_fwd_cstep n g Dm δ τ σ st i).2.1
      = (numclust_fwd_deathStep n g Dm δ σ (st.2.1, st.2.2) i).1 := rfl

private theorem numclust_fwd_cstep_dth {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (st : UFState n × UFState n × (Fin n → EReal))
    (i : Fin n) :
    (numclust_fwd_cstep n g Dm δ τ σ st i).2.2
      = (numclust_fwd_deathStep n g Dm δ σ (st.2.1, st.2.2) i).2 := rfl

/-- The τ-label projection of a coupled fold is the corresponding `ufStep` fold. -/
private theorem numclust_fwd_cRun_fst {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (l : List (Fin n))
    (init : UFState n × UFState n × (Fin n → EReal)) :
    (l.foldl (fun st k => numclust_fwd_cstep n g Dm δ τ σ st (σ k)) init).1
      = l.foldl (fun st k => ufStep g Dm δ τ σ st (σ k)) init.1 := by
  induction l generalizing init with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.foldl_cons]
    exact ih (numclust_fwd_cstep n g Dm δ τ σ init (σ k))

/-- The (plain-label, death-map) projection of a coupled fold is the corresponding
`numclust_fwd_deathStep` fold (the τ-label map does not affect the plain/death evolution). -/
private theorem numclust_fwd_cRun_snd {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (l : List (Fin n))
    (init : UFState n × UFState n × (Fin n → EReal)) :
    ((l.foldl (fun st k => numclust_fwd_cstep n g Dm δ τ σ st (σ k)) init).2.1,
     (l.foldl (fun st k => numclust_fwd_cstep n g Dm δ τ σ st (σ k)) init).2.2)
      = l.foldl (fun (st : UFState n × (Fin n → EReal)) k =>
            numclust_fwd_deathStep n g Dm δ σ st (σ k)) (init.2.1, init.2.2) := by
  obtain ⟨T, lab, dth⟩ := init
  induction l generalizing T lab dth with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.foldl_cons]
    exact ih (ufStep g Dm δ τ σ T (σ k))
      (numclust_fwd_deathStep n g Dm δ σ (lab, dth) (σ k)).1
      (numclust_fwd_deathStep n g Dm δ σ (lab, dth) (σ k)).2

/-- Projections of the full coupled run: its τ-label map is `ufRun`, and its
(plain-label, death-map) pair is `numclust_fwd_deathRun`. -/
private theorem numclust_fwd_cRun_proj (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) :
    (numclust_fwd_cRun n g Dm δ τ σ).1 = ufRun g Dm δ τ σ ∧
    ((numclust_fwd_cRun n g Dm δ τ σ).2.1, (numclust_fwd_cRun n g Dm δ τ σ).2.2)
      = numclust_fwd_deathRun n g Dm δ σ := by
  refine ⟨?_, ?_⟩
  · simp only [numclust_fwd_cRun, ufRun]
    exact numclust_fwd_cRun_fst (n := n) g Dm δ τ σ (List.finRange n).reverse
      ((fun _ => none), (fun _ => none), (fun _ => ⊥))
  · have h := numclust_fwd_cRun_snd (n := n) g Dm δ τ σ (List.finRange n).reverse
      ((fun _ => none), (fun _ => none), (fun _ => ⊥))
    simpa only [numclust_fwd_cRun, numclust_fwd_deathRun] using h

/-- The plain-sweep invariant core carried alongside the coupling invariant: processed-set
characterization, rootedness, "dead roots are not current roots" (NR), and "dead vertices
are absorbed (labelled)". -/
private def numclust_fwd_InvCore {n : ℕ} (g : Fin n → ℝ) (σ : Fin n ≃ Fin n) (t : ℕ)
    (lab : UFState n) (dth : Fin n → EReal) : Prop :=
  (∀ v : Fin n, (lab v).isSome = true ↔ t ≤ (σ.symm v : ℕ)) ∧
  (∀ v r : Fin n, lab v = some r → lab r = some r) ∧
  (∀ r : Fin n, (dth r : EReal) ≠ ⊥ → lab r ≠ some r) ∧
  (∀ r : Fin n, (dth r : EReal) ≠ ⊥ → (lab r).isSome = true)

/-- One plain-sweep step preserves the invariant core (threshold `t+1` → `t`): the
processed set grows by exactly the processed vertex, rootedness is preserved
(plain merge has no second `E`-merge), dead roots never become current roots, and
dead vertices stay absorbed. -/
private theorem numclust_fwd_InvCore_step {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n)
    (t : ℕ) (ht : t < n) (i : Fin n) (hiσ : σ.symm i = ⟨t, ht⟩)
    (lab : UFState n) (dth : Fin n → EReal)
    (hInv : numclust_fwd_InvCore g σ (t+1) lab dth) :
    numclust_fwd_InvCore g σ t
      (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1
      (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).2 := by
  obtain ⟨hI0, hI2, hNRcore, hDlab⟩ := hInv
  have hSymmI : (σ.symm i : ℕ) = t := by rw [hiσ]
  have hSymmEq : ∀ v : Fin n, (σ.symm v : ℕ) = t → v = i := by
    intro v h
    exact σ.symm.injective (Fin.val_injective (by rw [hSymmI]; exact h))
  have hlabi : lab i = none := by
    have hni : ¬ (t + 1 ≤ (σ.symm i : ℕ)) := by rw [hSymmI]; omega
    cases h : lab i with
    | none => rfl
    | some x => exact absurd ((hI0 i).mp (by rw [h]; simp)) hni
  have hdthi : dth i = ⊥ := by
    by_contra hne
    have hlab : (lab i).isSome = true := hDlab i hne
    rw [hlabi] at hlab
    simp at hlab
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- I0: processed set grows by exactly `i`
    intro v
    by_cases hS :
      (Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome) : Finset (Fin n)) = ∅
    · have hlab' : (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1
          = Function.update lab i (some i) := by
        simp only [numclust_fwd_deathStep, if_pos hS]
      rw [hlab']
      by_cases hvi : v = i
      · rw [hvi, Function.update_self]
        exact iff_of_true (by simp) (by simp [hSymmI])
      · simp only [Function.update_of_ne hvi]
        have hvne : (σ.symm v : ℕ) ≠ t := fun h => hvi (hSymmEq v h)
        constructor
        · intro his
          have hv := (hI0 v).mp his
          omega
        · intro hle
          exact (hI0 v).mpr (by omega)
    · -- merge: `i` is labelled, other labels only move between roots
      have hlab2form : ∀ w, (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1 w =
          (if w = i then some (numclust_fwd_R Dm δ σ lab i) else
            match lab w with
            | some r => if r ∈ numclust_fwd_M Dm δ σ lab i
              then some (numclust_fwd_R Dm δ σ lab i) else some r
            | none => none) := by
        intro w
        simp only [numclust_fwd_deathStep, if_neg hS]
        rfl
      rw [hlab2form v]
      by_cases hvi : v = i
      · rw [hvi, if_pos rfl]
        exact iff_of_true (by simp) (by simp [hSymmI])
      · rw [if_neg hvi]
        have hvne : (σ.symm v : ℕ) ≠ t := fun h => hvi (hSymmEq v h)
        cases hl : lab v with
        | none =>
          have hfn : ¬ (t + 1 ≤ (σ.symm v : ℕ)) := by
            intro hh
            exact absurd ((hI0 v).mpr hh) (by rw [hl]; simp)
          constructor
          · intro hf
            simp at hf
          · omega
        | some a =>
          constructor
          · intro _
            have hv := (hI0 v).mp (by rw [hl]; simp)
            omega
          · intro _
            dsimp only []
            by_cases hm : a ∈ numclust_fwd_M Dm δ σ lab i
            · rw [if_pos hm]; exact Option.isSome_some
            · rw [if_neg hm]; exact Option.isSome_some
  · -- I2: rootedness
    by_cases hS :
      (Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome) : Finset (Fin n)) = ∅
    · have hlab' : (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1
          = Function.update lab i (some i) := by
        simp only [numclust_fwd_deathStep, if_pos hS]
      rw [hlab']
      intro v r h
      by_cases hvi : v = i
      · rw [hvi, Function.update_self] at h
        simp only [Option.some.injEq] at h
        rw [← h, Function.update_self]
      · simp only [Function.update_of_ne hvi] at h
        have hI2v := hI2 v r h
        by_cases hri : r = i
        · rw [hri] at hI2v
          rw [hI2v] at hlabi
          exact absurd hlabi (by simp)
        · simp only [Function.update_of_ne hri, hI2v]
    · have hlb : (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1
          = (barStep g Dm δ σ (lab, (fun _ => (0 : ℕ∞))) i).1 :=
        numclust_fwd_step_fst_ne n g Dm δ σ lab dth (fun _ => (0 : ℕ∞)) i hS
      rw [hlb]
      exact numclust_fwd_barStep_rooted n g Dm δ σ lab (fun _ => (0 : ℕ∞)) i hI2 hlabi
  · -- I3 (NR): dead roots are not current roots
    intro r hr
    by_cases hS :
      (Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome) : Finset (Fin n)) = ∅
    · have hdth' : (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).2 = dth := by
        simp only [numclust_fwd_deathStep, if_pos hS]
      rw [hdth'] at hr
      by_cases hri : r = i
      · exfalso
        exact (hri ▸ hr) hdthi
      · have hlab' : (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1
            = Function.update lab i (some i) := by
          simp only [numclust_fwd_deathStep, if_pos hS]
        rw [hlab']
        simp only [Function.update_of_ne hri]
        exact hNRcore r hr
    · -- merge
      have hdthform : ∀ r, (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).2 r =
          (if r ∈ numclust_fwd_dying g Dm δ σ lab i then ((g i : EReal)) else dth r) := by
        intro r
        rw [numclust_fwd_deathStep_snd n g Dm δ σ lab dth i, if_neg hS]
      have hSne : (numclust_fwd_S Dm δ lab i).Nonempty := Finset.nonempty_of_ne_empty hS
      have hroot_mem : ∀ j ∈ numclust_fwd_S Dm δ lab i,
          lab (numclust_fwd_root lab j) = some (numclust_fwd_root lab j) := by
        intros j hj
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hj).2.2.2
        simp only [numclust_fwd_root, ha]
        exact hI2 j a ha
      have hMroot : ∀ m ∈ numclust_fwd_M Dm δ σ lab i, lab m = some m := by
        intros m hm
        rcases Finset.mem_insert.mp hm with hm' | hm'
        · rw [hm']; exact hroot_mem (firstProcessed σ (numclust_fwd_S Dm δ lab i) i)
            (numclust_fwd_fp_mem n σ (numclust_fwd_S Dm δ lab i) i hSne)
        · obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp hm'
          rw [← hjm]; exact hroot_mem j hjS
      have hMne : (numclust_fwd_M Dm δ σ lab i).Nonempty := ⟨_, Finset.mem_insert_self _ _⟩
      have hRm : numclust_fwd_R Dm δ σ lab i ∈ numclust_fwd_M Dm δ σ lab i :=
        numclust_fwd_fp_mem n σ (numclust_fwd_M Dm δ σ lab i) _ hMne
      have hlab2form : ∀ w, (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1 w =
          (if w = i then some (numclust_fwd_R Dm δ σ lab i) else
            match lab w with
            | some r => if r ∈ numclust_fwd_M Dm δ σ lab i
              then some (numclust_fwd_R Dm δ σ lab i) else some r
            | none => none) := by
        intro w
        simp only [numclust_fwd_deathStep, if_neg hS]
        rfl
      rw [hdthform r] at hr
      by_cases hrd : r ∈ numclust_fwd_dying g Dm δ σ lab i
      · -- newly dead: absorbed into `R ≠ r`
        obtain ⟨hrR, hrM⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hrd).1
        have hlabr : lab r = some r := hMroot r hrM
        have hri : r ≠ i := by
          intro h
          have hiM : i ∈ numclust_fwd_M Dm δ σ lab i := by rw [h] at hrM; exact hrM
          exact absurd (hMroot i hiM) (by rw [hlabi]; simp)
        rw [hlab2form r, if_neg hri, hlabr]
        dsimp only []
        rw [if_pos hrM]
        exact fun h => hrR (Option.some_inj.mp h).symm
      · rw [if_neg hrd] at hr
        have hlabr : lab r ≠ some r := hNRcore r hr
        rw [hlab2form r]
        by_cases hri : r = i
        · rw [if_pos hri]
          intro h
          have hRr : numclust_fwd_R Dm δ σ lab i = r := Option.some_inj.mp h
          have hrM : r ∈ numclust_fwd_M Dm δ σ lab i := by rw [← hRr]; exact hRm
          exact hlabr (hMroot r hrM)
        · rw [if_neg hri]
          cases hl : lab r with
          | none => exact fun h => by simp at h
          | some a =>
            dsimp only []
            by_cases hm : a ∈ numclust_fwd_M Dm δ σ lab i
            · rw [if_pos hm]
              intro h
              have hRr : numclust_fwd_R Dm δ σ lab i = r := Option.some_inj.mp h
              have hrM : r ∈ numclust_fwd_M Dm δ σ lab i := by rw [← hRr]; exact hRm
              exact hlabr (hMroot r hrM)
            · rw [if_neg hm]
              exact fun h => hlabr (hl.trans h)
  · -- I4: dead vertices stay absorbed (labelled)
    intro r hr
    by_cases hS :
      (Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome) : Finset (Fin n)) = ∅
    · have hdth' : (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).2 = dth := by
        simp only [numclust_fwd_deathStep, if_pos hS]
      rw [hdth'] at hr
      have hlab' : (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1
          = Function.update lab i (some i) := by
        simp only [numclust_fwd_deathStep, if_pos hS]
      rw [hlab']
      by_cases hri : r = i
      · exfalso
        exact (hri ▸ hr) hdthi
      · simp only [Function.update_of_ne hri]
        exact hDlab r hr
    · -- merge
      have hdthform : ∀ r, (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).2 r =
          (if r ∈ numclust_fwd_dying g Dm δ σ lab i then ((g i : EReal)) else dth r) := by
        intro r
        rw [numclust_fwd_deathStep_snd n g Dm δ σ lab dth i, if_neg hS]
      have hSne : (numclust_fwd_S Dm δ lab i).Nonempty := Finset.nonempty_of_ne_empty hS
      have hroot_mem : ∀ j ∈ numclust_fwd_S Dm δ lab i,
          lab (numclust_fwd_root lab j) = some (numclust_fwd_root lab j) := by
        intros j hj
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hj).2.2.2
        simp only [numclust_fwd_root, ha]
        exact hI2 j a ha
      have hMroot : ∀ m ∈ numclust_fwd_M Dm δ σ lab i, lab m = some m := by
        intros m hm
        rcases Finset.mem_insert.mp hm with hm' | hm'
        · rw [hm']; exact hroot_mem (firstProcessed σ (numclust_fwd_S Dm δ lab i) i)
            (numclust_fwd_fp_mem n σ (numclust_fwd_S Dm δ lab i) i hSne)
        · obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp hm'
          rw [← hjm]; exact hroot_mem j hjS
      have hlab2form : ∀ w, (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1 w =
          (if w = i then some (numclust_fwd_R Dm δ σ lab i) else
            match lab w with
            | some r => if r ∈ numclust_fwd_M Dm δ σ lab i
              then some (numclust_fwd_R Dm δ σ lab i) else some r
            | none => none) := by
        intro w
        simp only [numclust_fwd_deathStep, if_neg hS]
        rfl
      rw [hdthform r] at hr
      by_cases hrd : r ∈ numclust_fwd_dying g Dm δ σ lab i
      · obtain ⟨hrR, hrM⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hrd).1
        have hlabr : lab r = some r := hMroot r hrM
        have hri : r ≠ i := by
          intro h
          have hiM : i ∈ numclust_fwd_M Dm δ σ lab i := by rw [h] at hrM; exact hrM
          exact absurd (hMroot i hiM) (by rw [hlabi]; simp)
        rw [hlab2form r, if_neg hri, hlabr]
        dsimp only []
        rw [if_pos hrM]
        exact Option.isSome_some
      · rw [if_neg hrd] at hr
        have his := hDlab r hr
        rw [hlab2form r]
        by_cases hri : r = i
        · rw [if_pos hri]; exact Option.isSome_some
        · rw [if_neg hri]
          cases hl : lab r with
          | none => rw [hl] at his; simp at his
          | some a =>
            dsimp only []
            by_cases hm : a ∈ numclust_fwd_M Dm δ σ lab i
            · rw [if_pos hm]; exact Option.isSome_some
            · rw [if_neg hm]; exact Option.isSome_some

/-- The plain-sweep invariant core holds at every prefix of the private death sweep. -/
private theorem numclust_fwd_InvCore_fold (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) :
    ∀ j : ℕ, j ≤ n →
      numclust_fwd_InvCore g σ (n - j)
        (((List.finRange n).reverse.take j).foldl
          (fun (st : UFState n × (Fin n → EReal)) k =>
            numclust_fwd_deathStep n g Dm δ σ st (σ k))
          ((fun _ => none), (fun _ => ⊥))).1
        (((List.finRange n).reverse.take j).foldl
          (fun (st : UFState n × (Fin n → EReal)) k =>
            numclust_fwd_deathStep n g Dm δ σ st (σ k))
          ((fun _ => none), (fun _ => ⊥))).2 := by
  intro j hj
  induction j with
  | zero =>
    simp only [List.take_zero, List.foldl_nil]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v; simp
    · intro v r h; simp at h
    · intro r hr; exact absurd rfl hr
    · intro r hr; exact absurd rfl hr
  | succ j ih =>
    have hjn : j < n := by omega
    have hlen : List.length (List.finRange n).reverse = n := by
      rw [List.length_reverse, List.length_finRange]
    have hinst : j < (List.finRange n).reverse.length := by rw [hlen]; omega
    rw [List.take_succ_eq_append_getElem hinst]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hfin : ((List.finRange n).reverse)[j]'hinst = ⟨n - (j + 1), by omega⟩ := by
      rw [List.getElem_reverse hinst]
      rw [List.getElem_finRange (by rw [List.length_finRange]; omega)]
      exact Fin.val_injective (by simp [List.length_finRange, Fin.val_cast]; omega)
    rw [hfin]
    exact numclust_fwd_InvCore_step g Dm δ σ (n - (j + 1)) (by omega)
      (σ ⟨n - (j + 1), by omega⟩) (σ.symm_apply_apply _) _ _
      (by simpa only [show n - (j + 1) + 1 = n - j by omega] using ih (by omega))

/-! #### Merge-step membership and root lemmas (att34, ported from the reverse lane) -/

/-- A labelled δ-neighbour of `i` is self-labelled at its entry root. -/
private theorem numclust_fwd_S_root {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (lab : UFState n) (i j : Fin n)
    (hj : j ∈ numclust_fwd_S Dm δ lab i) :
    lab j = some ((lab j).getD j) := by
  have hisSome : (lab j).isSome := (Finset.mem_filter.mp hj).2.2.2
  rcases h : lab j with _ | x
  · simp [Option.isSome, h] at hisSome
  · simp only [h, Option.getD_some]

/-- Membership in the plain merge set `M`. -/
private theorem numclust_fwd_mem_M {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (lab : UFState n) (i r : Fin n) :
    r ∈ numclust_fwd_M Dm δ σ lab i ↔
      r = numclust_fwd_root lab (firstProcessed σ (numclust_fwd_S Dm δ lab i) i) ∨
      ∃ j ∈ numclust_fwd_S Dm δ lab i, numclust_fwd_root lab j = r := by
  simp only [numclust_fwd_M, Finset.mem_insert, Finset.mem_image]

/-- Every member of the plain merge set is a current plain root (when `S ≠ ∅`). -/
private theorem numclust_fwd_M_root {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (lab : UFState n) (i : Fin n)
    (hS : numclust_fwd_S Dm δ lab i ≠ ∅)
    (hI2 : ∀ v r : Fin n, lab v = some r → lab r = some r)
    (r : Fin n) (hr : r ∈ numclust_fwd_M Dm δ σ lab i) :
    lab r = some r := by
  have hSne : (numclust_fwd_S Dm δ lab i).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hS
  rcases (numclust_fwd_mem_M Dm δ σ lab i r).mp hr with heq | ⟨j, hjS, hrj⟩
  · have hfp : firstProcessed σ (numclust_fwd_S Dm δ lab i) i ∈
        numclust_fwd_S Dm δ lab i :=
      numclust_fwd_fp_mem n σ _ i hSne
    have hlabfp :
        lab (firstProcessed σ (numclust_fwd_S Dm δ lab i) i) =
          some ((lab (firstProcessed σ (numclust_fwd_S Dm δ lab i) i)).getD
            (firstProcessed σ (numclust_fwd_S Dm δ lab i) i)) :=
      numclust_fwd_S_root Dm δ lab i _ hfp
    rw [heq]
    exact hI2 _ _ hlabfp
  · have hlabj : lab j = some ((lab j).getD j) :=
      numclust_fwd_S_root Dm δ lab i j hjS
    rw [← hrj]
    exact hI2 _ _ hlabj

/-- The plain label part of a merge-branch death step, in named-piece form. -/
private theorem numclust_fwd_deathStep_lab_ne {n : ℕ} (g : Fin n → ℝ)
    (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (lab : UFState n) (dth : Fin n → EReal) (i : Fin n)
    (hS : (Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)
      : Finset (Fin n)) ≠ ∅) :
    (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1 =
      (fun v => if v = i then some (numclust_fwd_R Dm δ σ lab i)
        else match lab v with
          | some a => if a ∈ numclust_fwd_M Dm δ σ lab i then some (numclust_fwd_R Dm δ σ lab i)
              else some a
          | none => none) := by
  dsimp only [numclust_fwd_deathStep]
  rw [if_neg hS]
  rfl

/-- Coupling invariant at threshold `t`: τ-processed set, τ-rootedness, τ/plain refinement,
the per-root survivor characterization (Claim K) at the prefix, the dominance of recorded
deaths over future levels (A4), and NR (dead roots are not current plain roots). -/
private def numclust_fwd_FCI {n : ℕ} (g : Fin n → ℝ) (τ : ℝ) (σ : Fin n ≃ Fin n) (t : ℕ)
    (T lab : UFState n) (dth : Fin n → EReal) : Prop :=
  (∀ v : Fin n, (T v).isSome = true ↔ t ≤ (σ.symm v : ℕ)) ∧
  (∀ v r : Fin n, T v = some r → T r = some r) ∧
  (∀ v r : Fin n, T v = some r → lab v = lab r) ∧
  (∀ r : Fin n, (lab r = some r ∨
      ((dth r : EReal) ≠ ⊥ ∧ (dth r) + (τ : EReal) ≤ (g r : EReal))) → T r = some r) ∧
  (∀ r : Fin n, T r = some r →
      (lab r = some r ∨
        ((dth r : EReal) ≠ ⊥ ∧ (dth r) + (τ : EReal) ≤ (g r : EReal)))) ∧
  -- 6th (SPLIT, att37 re-scope): the old "τ-root owns its whole plain entry ∨
  -- prominent" form was FALSE (saddle: `r = Rτ ∉ Minf` has `T' i = some Rτ` but
  -- `lab' i = some Rinf ≠ some r`), and every informative re-form (prominence,
  -- reverse's real-death `dth ≠ ⊥ ∧ dth ≠ ⊤`, `lab = some r ∨ dth = ⊥`) is still
  -- refuted by the forward's strict-death remainders (tie-saddle keeps `dth = ⊥`
  -- with `lab ≠ some r`; small-gap winner keeps a real non-prominent death).
  -- CONSUMER TRACE (att36/att37, verified): conjunct 6 has NO downstream
  -- consumer — R_char reads only `.2.2.2.2.1` (Kfwd) and `.2.2.2.2.2.2.2.1` (NR);
  -- nothing reads `.2.2.2.2.2.1`. It is maintained purely for the CI induction,
  -- so it is re-scoped to the trivial form (weakest true form, mission-endorsed).
  -- If Kfwd is ever re-formed (e.g. with a remainder disjunct + an empty-at-0
  -- discharge), mirror that form here.
  (∀ r : Fin n, T r = some r → True) ∧
  (∀ r : Fin n, (dth r : EReal) ≠ ⊥ →
      ∀ k : Fin n, (k : ℕ) < t → (g (σ k) : EReal) ≤ dth r) ∧
  (∀ r : Fin n, (dth r : EReal) ≠ ⊥ → lab r ≠ some r) ∧
  -- 9th (CI-ELD, added for the Kback port): every plain entry's root is the
  -- σ-eldest (max-`g`, max-`σ.symm`) member of its own entry.  Maintained by the
  -- elder rule; used for the redirect comparisons (Rinf ∈ Mτ ⇒ Rτ = Rinf chains).
  (∀ v r : Fin n, lab v = some r → (σ.symm v : ℕ) ≤ (σ.symm r : ℕ))

/-- One coupled step preserves the coupling invariant (threshold `t+1` → `t`), given the
plain-sweep invariant core at `t+1`. Mirrors `numclust_rev_CI_step`; the merge-branch case
analysis rhymes with the reverse lane's proven peak/merge branches. -/
private theorem numclust_fwd_cstep_CIs {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ)
    (t : ℕ) (ht : t < n) (i : Fin n) (hiσ : σ.symm i = ⟨t, ht⟩)
    (T lab : UFState n) (dth : Fin n → EReal)
    (hFCI : numclust_fwd_FCI g τ σ (t+1) T lab dth)
    (hInv : numclust_fwd_InvCore g σ (t+1) lab dth) :
    numclust_fwd_FCI g τ σ t
      (numclust_fwd_cstep n g Dm δ τ σ (T, lab, dth) i).1
      (numclust_fwd_cstep n g Dm δ τ σ (T, lab, dth) i).2.1
      (numclust_fwd_cstep n g Dm δ τ σ (T, lab, dth) i).2.2 := by
  obtain ⟨hA1, hA2, hREF, hKback, hKfwd, hSPLIT, hA4, hNR, hEl⟩ := hFCI
  obtain ⟨hI0, hI2, hNRcore, hDlab⟩ := hInv
  have hSymmI : (σ.symm i : ℕ) = t := by rw [hiσ]
  have hSymmEq : ∀ v : Fin n, (σ.symm v : ℕ) = t → v = i := by
    intro v h
    exact σ.symm.injective (Fin.val_injective (by rw [hSymmI]; exact h))
  have hmono : ∀ x y : Fin n, (σ.symm x : ℕ) ≤ (σ.symm y : ℕ) → g x ≤ g y := by
    intro x y h
    have hxy : σ.symm x ≤ σ.symm y := Fin.le_def.mpr h
    simpa using hσ hxy
  have hTi : T i = none := by
    have hni : ¬ (t + 1 ≤ (σ.symm i : ℕ)) := by rw [hSymmI]; omega
    cases h : T i with
    | none => rfl
    | some x => exact absurd ((hA1 i).mp (by rw [h]; simp)) hni
  have hlabi : lab i = none := by
    have hni : ¬ (t + 1 ≤ (σ.symm i : ℕ)) := by rw [hSymmI]; omega
    cases h : lab i with
    | none => rfl
    | some x => exact absurd ((hI0 i).mp (by rw [h]; simp)) hni
  have hSeq :
      (Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (T j).isSome) : Finset (Fin n))
        = Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome) := by
    apply Finset.filter_congr
    intro j _
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (hI0 j).mpr ((hA1 j).mp h3)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (hA1 j).mpr ((hI0 j).mp h3)⟩
  rw [numclust_fwd_cstep_uf, numclust_fwd_cstep_lab, numclust_fwd_cstep_dth]
  by_cases hS :
    (Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome) : Finset (Fin n)) = ∅
  · -- PEAK: `i` starts a fresh entry in both sweeps; no merge, no death.
    have hST :
        (Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (T j).isSome) : Finset (Fin n))
          = ∅ := by rw [hSeq]; exact hS
    have hT' : ufStep g Dm δ τ σ T i = Function.update T i (some i) := by
      simp only [ufStep, if_pos hST]
    have hlab' :
        (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1 = Function.update lab i (some i) := by
      simp only [numclust_fwd_deathStep, if_pos hS]
    have hdth' : (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).2 = dth := by
      simp only [numclust_fwd_deathStep, if_pos hS]
    rw [hT', hlab', hdth']
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- A1: processed set grows by `i`
      intro v
      by_cases hvi : v = i
      · rw [hvi, Function.update_self]
        exact iff_of_true (by simp) (by simp [hSymmI])
      · simp only [Function.update_of_ne hvi]
        have hvne : (σ.symm v : ℕ) ≠ t := fun h => hvi (hSymmEq v h)
        constructor
        · intro his
          have hv := (hA1 v).mp his
          omega
        · intro hle
          exact (hA1 v).mpr (by omega)
    · -- A2: τ-root closure
      intro v r h
      by_cases hvi : v = i
      · rw [hvi, Function.update_self] at h
        simp only [Option.some.injEq] at h
        rw [← h, Function.update_self]
      · simp only [Function.update_of_ne hvi] at h
        have hA2v := hA2 v r h
        by_cases hri : r = i
        · rw [hri] at hA2v
          rw [hA2v] at hTi
          exact absurd hTi (by simp)
        · simp only [Function.update_of_ne hri, hA2v]
    · -- REF: τ-entry inside plain-entry
      intro v r h
      by_cases hvi : v = i
      · rw [hvi, Function.update_self] at h
        simp only [Option.some.injEq] at h
        rw [hvi, ← h]
      · simp only [Function.update_of_ne hvi] at h
        have hA2v := hA2 v r h
        by_cases hri : r = i
        · rw [hri] at hA2v
          rw [hA2v] at hTi
          exact absurd hTi (by simp)
        · simp only [Function.update_of_ne hvi, Function.update_of_ne hri]
          exact hREF v r h
    · -- Kback: plain-root ∨ prominent ⇒ τ-root
      intro r h
      by_cases hri : r = i
      · rw [hri, Function.update_self]
      · simp only [Function.update_of_ne hri]
        simp only [Function.update_of_ne hri] at h
        rcases h with h | ⟨h1, h2⟩
        · exact hKback r (Or.inl h)
        · exact hKback r (Or.inr ⟨h1, h2⟩)
    · -- Kfwd: τ-root ⇒ plain-root ∨ prominent
      intro r h
      by_cases hri : r = i
      · left
        rw [hri, Function.update_self]
      · simp only [Function.update_of_ne hri] at h
        rcases hKfwd r h with hk | ⟨h1, h2⟩
        · refine Or.inl ?_
          simp only [Function.update_of_ne hri]
          exact hk
        · simp only [Function.update_of_ne hri]
          exact Or.inr ⟨h1, h2⟩
    · -- SPLIT: re-scoped (att37) to the trivial form — no downstream consumer.
      intro r h
      trivial
    · -- A4: recorded deaths dominate all future levels (dth' = dth unchanged)
      intro r hr k hk
      exact hA4 r hr k (by omega)
    · -- NR: dead roots are not current plain roots (dth' = dth unchanged)
      intro r hr
      by_cases hri : r = i
      · exfalso
        have hdi : dth i ≠ ⊥ := hri ▸ hr
        have hlab : (lab i).isSome = true := hDlab i hdi
        rw [hlabi] at hlab
        simp at hlab
      · simp only [Function.update_of_ne hri]
        exact hNRcore r hr
    · -- CI-ELD: elder rule preserved; `i` is a fresh self-labelled peak (dth'=dth).
      intro v r h
      by_cases hvi : v = i
      · rw [hvi, Function.update_self] at h
        simp only [Option.some.injEq] at h
        rw [hvi, ← h]
      · simp only [Function.update_of_ne hvi] at h
        exact hEl v r h
  · -- MERGE (plain S ≠ ∅): the τ-sweep else-branch (with the E-merge) coupled to the
    -- plain death-step else-branch. See /tmp/opencode/agents/numclust_fwd_explanation.md
    -- (R_char plan) and /tmp/opencode/agents/numclust_rev_explanation.md §"CI_step case
    -- analysis" for the per-component case tree (the Hroots characterization
    -- `T' r = some r ↔ (T r = some r ∧ r ∉ Mτ)` drives REF/Kback/Kfwd/SPLIT).
    have hST :
        (Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (T j).isSome) : Finset (Fin n))
          ≠ ∅ := by rw [hSeq]; exact hS
    -- τ-side bridge (mirrors numclust_rev_cstep_CIs): unfold `ufStep` to the explicit
    -- `T'my` form over Sτ / Mτ / Rτ / Eτ. Shared by REF/Kback/Kfwd/SPLIT. The τ-filtered
    -- merge set Mτ (inside ufStep) is distinct from the plain unfiltered merge set
    -- `numclust_fwd_M` — this is the ufStep/deathStep asymmetry.
    set Sτ := Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (T j).isSome) with hSτ
    set riτ := (T (firstProcessed σ Sτ i)).getD (firstProcessed σ Sτ i) with hriτ
    set Mτ := insert riτ
        ((Sτ.image (fun j => (T j).getD j)).filter (fun r => g r - g i < τ)) with hMτ
    set Rτ := firstProcessed σ Mτ riτ with hRτ
    set hl2 : Fin n → Option (Fin n) := fun u =>
      if u = i then some Rτ
      else match T u with
        | some x => if x ∈ Mτ then some Rτ else some x
        | none => none with hhl2
    set Eτ := firstProcessed σ (Sτ.image (fun j => (hl2 j).getD j)) Rτ with hEτ
    set T'my : UFState n :=
      if Eτ ≠ Rτ ∧ g Rτ - g i < τ then
        (fun w => if (if w = i then some Rτ
            else match T w with
              | some x => if x ∈ Mτ then some Rτ else some x
              | none => none) = some Rτ then some Eτ
              else (if w = i then some Rτ
                else match T w with
                  | some x => if x ∈ Mτ then some Rτ else some x
                  | none => none))
        else (fun w => if w = i then some Rτ
                else match T w with
                  | some x => if x ∈ Mτ then some Rτ else some x
                  | none => none) with hT'my
    have hT'uf : ∀ w, ufStep g Dm δ τ σ T i w = T'my w := by
      intro w
      have hSτne : Sτ ≠ ∅ := by rw [hSτ]; exact hST
      simp only [ufStep]
      simp only [← hSτ, ← hriτ, ← hMτ, ← hRτ]
      rw [if_neg hSτne]
      rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- A1: τ-processed set grows by `i` (ufStep labels `i`, preserves isSome off `i`)
      intro v
      by_cases hvi : v = i
      · subst hvi
        rw [numclust_fwd_ufStep_isSome_i]
        simp [hSymmI]
      · rw [numclust_fwd_ufStep_isSome n g Dm δ τ σ T i v hvi]
        have hvne : (σ.symm v : ℕ) ≠ t := fun h => hvi (hSymmEq v h)
        constructor
        · intro his
          have hv := (hA1 v).mp his
          omega
        · intro hle
          exact (hA1 v).mpr (by omega)
    · -- A2: τ-root closure — whole-step, via the hoisted ufStep-rootedness lemma
      exact numclust_fwd_ufStep_rooted n g Dm δ τ σ T i hA2 hTi
    · -- REF: τ-entry inside plain-entry persists through the τ/plain merges.
      -- Ported from the reverse lane's C3 (label-agreement); form-independent.
      -- The τ-merge (Mτ) is a sub-merge of the plain merge (Minf), and label
      -- constancy on τ-entries (hREF) lifts every τ-redirect to the plain redirect.
      intro v r h
      simp only [hT'uf, hT'my] at h
      set Rinf := numclust_fwd_R Dm δ σ lab i with hRinfdef
      set Minf := numclust_fwd_M Dm δ σ lab i with hMinfdef
      have hlab'uf : ∀ w, (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1 w =
          (if w = i then some Rinf
            else match lab w with
              | some a => if a ∈ Minf then some Rinf else some a
              | none => none) := by
        intro w
        rw [numclust_fwd_deathStep_lab_ne g Dm δ σ lab dth i hS]
      rw [hlab'uf v, hlab'uf r]
      -- shared spine facts (Sτ members are δ-close labelled plain roots in Minf)
      have hSτne : Sτ.Nonempty := by rw [hSτ]; exact Finset.nonempty_iff_ne_empty.mpr hST
      have hSτmem : ∀ j ∈ Sτ, j ≠ i ∧ (T j).isSome = true := by
        intro j hj; rw [hSτ] at hj
        exact ⟨(Finset.mem_filter.mp hj).2.1, (Finset.mem_filter.mp hj).2.2.2⟩
      have hjSlab : ∀ j ∈ Sτ, j ∈ numclust_fwd_S Dm δ lab i := by
        intro j hj
        rw [hSeq] at hj
        exact hj
      have hlabjS : ∀ j ∈ Sτ, lab j = some ((lab j).getD j) :=
        fun j hj => numclust_fwd_S_root Dm δ lab i j (hjSlab j hj)
      have hrMS : ∀ j ∈ Sτ, (lab j).getD j ∈ Minf := by
        intro j hj
        rw [hMinfdef]
        exact (numclust_fwd_mem_M Dm δ σ lab i _).mpr (Or.inr ⟨j, hjSlab j hj, rfl⟩)
      have hKey : ∀ m ∈ Mτ,
          (if m = i then some Rinf
            else match lab m with
              | some a => if a ∈ Minf then some Rinf else some a
              | none => none) = some Rinf := by
        intro m hm
        have hwit : ∃ j ∈ Sτ, T j = some m := by
          rw [hMτ] at hm
          rcases Finset.mem_insert.mp hm with rfl | hm'
          · refine ⟨firstProcessed σ Sτ i, numclust_fwd_fp_mem n σ _ i hSτne, ?_⟩
            have hsome : (T (firstProcessed σ Sτ i)).isSome = true :=
              (hSτmem _ (numclust_fwd_fp_mem n σ _ i hSτne)).2
            cases hTf : T (firstProcessed σ Sτ i) with
            | none => rw [hTf] at hsome; simp at hsome
            | some s =>
              have hri : riτ = s := by rw [hriτ, hTf]; simp
              rw [hri]
          · have him := (Finset.mem_filter.mp hm').1
            obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp him
            have hsome : (T j).isSome = true := (hSτmem j hjS).2
            cases hTj : T j with
            | none => rw [hTj] at hsome; simp at hsome
            | some s =>
              have hget : (T j).getD j = s := by rw [hTj]; simp
              have hms : m = s := hjm.symm.trans hget
              refine ⟨j, hjS, ?_⟩
              rw [hms]; exact hTj
        obtain ⟨j, hjS, hjT⟩ := hwit
        have hlabj : lab j = some ((lab j).getD j) := hlabjS j hjS
        have hrM : (lab j).getD j ∈ Minf := hrMS j hjS
        have hlabm : lab m = some ((lab j).getD j) := by
          rw [← hREF j m hjT]; exact hlabj
        by_cases hmi : m = i
        · rw [hmi, if_pos rfl]
        · rw [if_neg hmi, hlabm]
          show (if (lab j).getD j ∈ Minf then some Rinf else (lab j).getD j) = some Rinf
          rw [if_pos hrM]
      have hLR : ∀ w s, lab w = some s → s ∈ Minf →
          (if w = i then some Rinf
            else match lab w with
              | some a => if a ∈ Minf then some Rinf else some a
              | none => none) = some Rinf := by
        intro w s hws hsM
        by_cases hwi : w = i
        · rw [hwi, if_pos rfl]
        · rw [if_neg hwi, hws]
          show (if s ∈ Minf then some Rinf else s) = some Rinf
          rw [if_pos hsM]
      have hLfix : ∀ w y, w ≠ i → y ≠ i → lab w = lab y →
          (if w = i then some Rinf
            else match lab w with
              | some a => if a ∈ Minf then some Rinf else some a
              | none => none) =
          (if y = i then some Rinf
            else match lab y with
              | some a => if a ∈ Minf then some Rinf else some a
              | none => none) := by
        intro w y hw hy hwl
        rw [if_neg hw, if_neg hy, hwl]
      have hI :
          (if i = i then some Rinf
            else match lab i with
              | some a => if a ∈ Minf then some Rinf else some a
              | none => none) = some Rinf := by
        rw [if_pos rfl]
      have hPre : ∀ x ∈ Mτ, ∃ j ∈ Sτ, T j = some x := by
        intro x hx
        rw [hMτ] at hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · refine ⟨firstProcessed σ Sτ i, numclust_fwd_fp_mem n σ _ i hSτne, ?_⟩
          have hsome : (T (firstProcessed σ Sτ i)).isSome = true :=
            (hSτmem _ (numclust_fwd_fp_mem n σ _ i hSτne)).2
          cases hTf : T (firstProcessed σ Sτ i) with
          | none => rw [hTf] at hsome; simp at hsome
          | some s =>
            have hri : riτ = s := by rw [hriτ, hTf]; simp
            rw [hri]
        · have him := (Finset.mem_filter.mp hx').1
          obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp him
          have hsome : (T j).isSome = true := (hSτmem j hjS).2
          cases hTj : T j with
          | none => rw [hTj] at hsome; simp at hsome
          | some s =>
            have hget : (T j).getD j = s := by rw [hTj]; simp
            have hxs : x = s := hjm.symm.trans hget
            refine ⟨j, hjS, ?_⟩
            rw [hxs]; exact hTj
      have hMτne : Mτ.Nonempty := by rw [hMτ]; exact Finset.insert_nonempty _ _
      have hRτmem : Rτ ∈ Mτ := by rw [hRτ]; exact numclust_fwd_fp_mem n σ _ _ hMτne
      have hVEτh : Eτ ≠ Rτ →
          (if Eτ = i then some Rinf
            else match lab Eτ with
              | some a => if a ∈ Minf then some Rinf else some a
              | none => none) = some Rinf := by
        intro hER
        have hmne : (Sτ.image (fun j => (hl2 j).getD j)).Nonempty := hSτne.image _
        have hEmem : Eτ ∈ Sτ.image (fun j => (hl2 j).getD j) := by
          rw [hEτ]; exact numclust_fwd_fp_mem n σ _ Rτ hmne
        obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp hEmem
        obtain ⟨hjnei, hsome⟩ := hSτmem j hjS
        cases hTj : T j with
        | none => rw [hTj] at hsome; simp at hsome
        | some s =>
          have hlj : (hl2 j).getD j = (if s ∈ Mτ then some Rτ else some s).getD j := by
            simp only [hhl2, if_neg hjnei, hTj]
          by_cases hsM : s ∈ Mτ
          · have hEE : Eτ = Rτ := by rw [← hjm]; beta_reduce; rw [hlj]; simp [hsM]
            exact absurd hEE hER
          · have hEs : Eτ = s := by rw [← hjm]; beta_reduce; rw [hlj]; simp [hsM]
            have hjTE : T j = some Eτ := by rw [hEs]; exact hTj
            exact hLR Eτ ((lab j).getD j)
              (by rw [← hREF j Eτ hjTE]; exact hlabjS j hjS) (hrMS j hjS)
      by_cases hvi : v = i
      · rw [hvi] at h
        split_ifs at h with hE
        · beta_reduce at h
          have hBi : (if i = i then some Rτ else (match T i with
              | some x => if x ∈ Mτ then some Rτ else some x | none => none)) = some Rτ := by
            simp
          rw [hBi] at h
          simp at h
          rw [hvi, ← h]
          rw [hI, hVEτh hE.1]
        · beta_reduce at h
          have hBi : (if i = i then some Rτ else (match T i with
              | some x => if x ∈ Mτ then some Rτ else some x | none => none)) = some Rτ := by
            simp
          rw [hBi] at h
          simp at h
          rw [hvi, ← h]
          rw [hI, hKey Rτ hRτmem]
      · split_ifs at h with hE
        · beta_reduce at h
          cases hT : T v with
          | none => rw [hT, if_neg hvi] at h; simp at h
          | some x =>
            rw [hT, if_neg hvi] at h
            by_cases hxM : x ∈ Mτ
            · simp [hxM] at h
              rw [← h]
              obtain ⟨j, hjS, hjTx⟩ := hPre x hxM
              rw [hLR v ((lab j).getD j)
                (by rw [hREF v x hT, ← hREF j x hjTx]; exact hlabjS j hjS) (hrMS j hjS),
                hVEτh hE.1]
            · by_cases hxR : x = Rτ
              · exact absurd (hxR ▸ hRτmem) hxM
              · simp only [if_neg hxM, if_neg hxR, Option.some.injEq] at h
                rw [← h]
                have hxroot : T x = some x := hA2 v x hT
                have hxnei : x ≠ i := by
                  intro hxi; rw [hxi] at hxroot
                  exact absurd hxroot (by rw [hTi]; simp)
                exact hLfix v x hvi hxnei (hREF v x hT)
        · beta_reduce at h
          cases hT : T v with
          | none => rw [hT, if_neg hvi] at h; simp at h
          | some x =>
            rw [hT, if_neg hvi] at h
            by_cases hxM : x ∈ Mτ
            · simp [hxM] at h
              rw [← h]
              obtain ⟨j, hjS, hjTx⟩ := hPre x hxM
              rw [hLR v ((lab j).getD j)
                (by rw [hREF v x hT, ← hREF j x hjTx]; exact hlabjS j hjS) (hrMS j hjS),
                hKey Rτ hRτmem]
            · simp only [if_neg hxM, Option.some.injEq] at h
              rw [← h]
              have hxroot : T x = some x := hA2 v x hT
              have hxnei : x ≠ i := by
                intro hxi; rw [hxi] at hxroot
                exact absurd hxroot (by rw [hTi]; simp)
              exact hLfix v x hvi hxnei (hREF v x hT)
    · -- Kback: plain-root ∨ prominent-after ⇒ τ-root.
      -- Ported from the reverse lane's C4; adapted to this file's 2-part prominence
      -- form and STRICT-death `dying` set (subtlety #2). The Case B `Rinf ∈ Mτ`
      -- sub-case uses the att29 chains (CI-ELD `hEl` + `firstProcessed_le`).
      intro r hr
      set Rinf := numclust_fwd_R Dm δ σ lab i with hRinfdef
      set Minf := numclust_fwd_M Dm δ σ lab i with hMinfdef
      have hlab'uf : ∀ w, (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1 w =
          (if w = i then some Rinf
            else match lab w with
              | some a => if a ∈ Minf then some Rinf else some a
              | none => none) := by
        intro w
        rw [numclust_fwd_deathStep_lab_ne g Dm δ σ lab dth i hS]
      have hdth' : ∀ w, (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).2 w =
          (if w ∈ numclust_fwd_dying g Dm δ σ lab i then ((g i : EReal)) else dth w) := by
        intro w
        rw [numclust_fwd_deathStep_snd n g Dm δ σ lab dth i, if_neg hS]
      have hSτne : Sτ.Nonempty := by rw [hSτ]; exact Finset.nonempty_iff_ne_empty.mpr hST
      have hSτmem : ∀ j ∈ Sτ, j ≠ i ∧ (T j).isSome = true := by
        intro j hj; rw [hSτ] at hj
        exact ⟨(Finset.mem_filter.mp hj).2.1, (Finset.mem_filter.mp hj).2.2.2⟩
      have hjSlab : ∀ j ∈ Sτ, j ∈ numclust_fwd_S Dm δ lab i := by
        intro j hj; rw [hSeq] at hj; exact hj
      have hlabjS : ∀ j ∈ Sτ, lab j = some ((lab j).getD j) :=
        fun j hj => numclust_fwd_S_root Dm δ lab i j (hjSlab j hj)
      have hrMS : ∀ j ∈ Sτ, (lab j).getD j ∈ Minf := by
        intro j hj; rw [hMinfdef]
        exact (numclust_fwd_mem_M Dm δ σ lab i _).mpr (Or.inr ⟨j, hjSlab j hj, rfl⟩)
      have hMroot : ∀ s : Fin n, s ∈ Minf → lab s = some s :=
        fun s hs => numclust_fwd_M_root Dm δ σ lab i hS hI2 s hs
      have hMne : Minf.Nonempty := by rw [hMinfdef]; exact Finset.insert_nonempty _ _
      have hRinfmem : Rinf ∈ Minf :=
        numclust_fwd_fp_mem n σ Minf
          (numclust_fwd_root lab (firstProcessed σ (numclust_fwd_S Dm δ lab i) i)) hMne
      have hRinfroot : lab Rinf = some Rinf := hMroot Rinf hRinfmem
      have hiM : i ∉ Minf := by
        rw [hMinfdef]; intro h
        have hSne : (numclust_fwd_S Dm δ lab i).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hS
        rcases (numclust_fwd_mem_M Dm δ σ lab i i).mp h with heq | ⟨j, hjS, hrj⟩
        · have hfp := numclust_fwd_fp_mem n σ (numclust_fwd_S Dm δ lab i) i hSne
          have hlabfp := numclust_fwd_S_root Dm δ lab i _ hfp
          have heq' : i = (lab (firstProcessed σ (numclust_fwd_S Dm δ lab i) i)).getD
              (firstProcessed σ (numclust_fwd_S Dm δ lab i) i) := heq
          rw [← heq'] at hlabfp
          exact absurd (hI2 _ _ hlabfp) (by rw [hlabi]; simp)
        · have hlabj := numclust_fwd_S_root Dm δ lab i j hjS
          have hrj' : (lab j).getD j = i := hrj
          rw [hrj'] at hlabj
          exact absurd (hI2 _ _ hlabj) (by rw [hlabi]; simp)
      have hMτroot : ∀ m ∈ Mτ, T m = some m ∧ m ≠ i := by
        intro m hm
        rw [hMτ] at hm
        rcases Finset.mem_insert.mp hm with rfl | hm'
        · obtain ⟨_, hsome⟩ :=
            hSτmem _ (by rw [hSτ]; exact numclust_fwd_fp_mem n σ _ i hSτne)
          cases hTf : T (firstProcessed σ Sτ i) with
          | none => rw [hTf] at hsome; simp at hsome
          | some s =>
            have hri : riτ = s := by rw [hriτ, hTf]; simp
            refine ⟨?_, ?_⟩
            · rw [hri]; exact hA2 _ _ hTf
            · rw [hri]; intro hsi; rw [hsi] at hTf
              exact absurd (hA2 _ _ hTf) (by rw [hTi]; simp)
        · have him := (Finset.mem_filter.mp hm').1
          obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp him
          obtain ⟨_, hsome⟩ := hSτmem j hjS
          cases hTj : T j with
          | none => rw [hTj] at hsome; simp at hsome
          | some s =>
            have hget : (T j).getD j = s := by rw [hTj]; simp
            rw [hget] at hjm
            rw [← hjm]
            refine ⟨?_, ?_⟩
            · exact hA2 _ _ hTj
            · intro hsi; rw [hsi] at hTj
              exact absurd (hA2 _ _ hTj) (by rw [hTi]; simp)
      have hRτmem : Rτ ∈ Mτ := by
        rw [hRτ]
        exact numclust_fwd_fp_mem n σ _ _ (by rw [hMτ]; exact Finset.insert_nonempty _ _)
      have hRτroot : T Rτ = some Rτ := (hMτroot Rτ hRτmem).1
      have hRτnei : Rτ ≠ i := (hMτroot Rτ hRτmem).2
      have hLR : ∀ w s, lab w = some s → s ∈ Minf →
          (if w = i then some Rinf
            else match lab w with
              | some a => if a ∈ Minf then some Rinf else some a
              | none => none) = some Rinf := by
        intro w s hws hsM
        by_cases hwi : w = i
        · rw [hwi, if_pos rfl]
        · rw [if_neg hwi, hws]
          show (if s ∈ Minf then some Rinf else s) = some Rinf
          rw [if_pos hsM]
      have hI :
          (if i = i then some Rinf
            else match lab i with
              | some a => if a ∈ Minf then some Rinf else some a
              | none => none) = some Rinf := by
        rw [if_pos rfl]
      have hMτpre : ∀ m ∈ Mτ, ∃ j ∈ Sτ, T j = some m := by
        intro m hm
        rw [hMτ] at hm
        rcases Finset.mem_insert.mp hm with rfl | hm'
        · refine ⟨firstProcessed σ Sτ i, numclust_fwd_fp_mem n σ _ i hSτne, ?_⟩
          have hsome : (T (firstProcessed σ Sτ i)).isSome = true :=
            (hSτmem _ (numclust_fwd_fp_mem n σ _ i hSτne)).2
          cases hTf : T (firstProcessed σ Sτ i) with
          | none => rw [hTf] at hsome; simp at hsome
          | some s =>
            have hri : riτ = s := by rw [hriτ, hTf]; simp
            rw [hri]
        · have him := (Finset.mem_filter.mp hm').1
          obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp him
          have hsome : (T j).isSome = true := (hSτmem j hjS).2
          cases hTj : T j with
          | none => rw [hTj] at hsome; simp at hsome
          | some s =>
            have hget : (T j).getD j = s := by rw [hTj]; simp
            have hms : m = s := hjm.symm.trans hget
            refine ⟨j, hjS, ?_⟩
            rw [hms]; exact hTj
      rcases hr with hlab | hprom
      · -- lab' r = some r.
        rw [hlab'uf r] at hlab
        by_cases hri : r = i
        · rw [hri] at hlab
          rw [hI] at hlab
          simp only [Option.some.injEq] at hlab
          exact (hiM (by rw [← hlab]; exact hRinfmem)).elim
        · rw [if_neg hri] at hlab
          cases hlr : lab r with
          | none => rw [hlr] at hlab; simp at hlab
          | some a =>
            rw [hlr] at hlab
            change (if a ∈ Minf then some Rinf else some a) = some r at hlab
            by_cases haM : a ∈ Minf
            · -- Case B: the redirect fires, Rinf = r.
              rw [if_pos haM] at hlab
              simp only [Option.some.injEq] at hlab
              have hrm : r ∈ Minf := by rw [← hlab]; exact hRinfmem
              have hlabr : lab r = some r := hMroot r hrm
              have hTr_r : T r = some r := hKback r (Or.inl hlabr)
              by_cases hRinfMτ : Rinf ∈ Mτ
              · -- att29 chains: Rinf ∈ Mτ ⟹ Rτ = Rinf and Eτ = Rτ (no demotion).
                have hRinfEldest : ∀ s ∈ Minf, (σ.symm s : ℕ) ≤ (σ.symm Rinf : ℕ) := by
                  intro s hs
                  have hle := numclust_fwd_firstProcessed_le σ Minf
                    (numclust_fwd_root lab (firstProcessed σ (numclust_fwd_S Dm δ lab i) i))
                    hMne s hs
                  rw [hRinfdef]
                  exact hle
                have hrootle : ∀ j ∈ Sτ,
                    (σ.symm ((T j).getD j) : ℕ) ≤ (σ.symm Rinf : ℕ) := by
                  intro j hjS
                  have hls : lab j = some ((lab j).getD j) := hlabjS j hjS
                  have hpjM : (lab j).getD j ∈ Minf := hrMS j hjS
                  have hiso : (T j).isSome = true := (hSτmem j hjS).2
                  cases hTj : T j with
                  | none => rw [hTj] at hiso; simp at hiso
                  | some s =>
                    have hlm : lab s = some ((lab j).getD j) := by
                      rw [← hREF j s hTj]; exact hls
                    have hle1 : (σ.symm s : ℕ) ≤ (σ.symm ((lab j).getD j) : ℕ) :=
                      hEl s _ hlm
                    show (σ.symm s : ℕ) ≤ (σ.symm Rinf : ℕ)
                    exact hle1.trans (hRinfEldest _ hpjM)
                have hMτle : ∀ m ∈ Mτ, (σ.symm m : ℕ) ≤ (σ.symm Rinf : ℕ) := by
                  intro m hm
                  obtain ⟨j, hjS, hjT⟩ := hMτpre m hm
                  have hle := hrootle j hjS
                  have hget : (T j).getD j = m := by rw [hjT]; simp
                  rw [hget] at hle
                  exact hle
                have hRτRinf : Rτ = Rinf := by
                  rw [hRτ]
                  have hne : Mτ.Nonempty := by rw [hMτ]; exact Finset.insert_nonempty _ _
                  simp only [firstProcessed, dif_pos hne]
                  have hrimem : σ.symm Rinf ∈ Mτ.image σ.symm :=
                    Finset.mem_image.mpr ⟨Rinf, hRinfMτ, rfl⟩
                  have hmax : (Mτ.image σ.symm).max' (hne.image _) = σ.symm Rinf :=
                    (Finset.max'_eq_iff (Mτ.image σ.symm) (hne.image _) (σ.symm Rinf)).mpr
                      ⟨hrimem,
                        fun b hb => by
                          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hb
                          exact Fin.le_iff_val_le_val.mpr (hMτle m hm)⟩
                  rw [hmax, σ.apply_symm_apply]
                have hEτRτ : Eτ = Rτ := by
                  have hImgne : (Sτ.image (fun j => (hl2 j).getD j)).Nonempty :=
                    hSτne.image _
                  have hEmem : Eτ ∈ Sτ.image (fun j => (hl2 j).getD j) := by
                    rw [hEτ]; exact numclust_fwd_fp_mem n σ _ Rτ hImgne
                  obtain ⟨j₀, hj₀S, hj₀T⟩ := hMτpre Rinf hRinfMτ
                  have hj₀i : j₀ ≠ i := (hSτmem j₀ hj₀S).1
                  have hatt : Rτ ∈ Sτ.image (fun j => (hl2 j).getD j) := by
                    refine Finset.mem_image.mpr ⟨j₀, hj₀S, ?_⟩
                    have h0 : (hl2 j₀).getD j₀ = Rτ := by
                      simp only [hhl2, if_neg hj₀i, hj₀T]
                      rw [if_pos hRinfMτ]
                      simp
                    exact h0
                  have hle1 : (σ.symm Rτ : ℕ) ≤ (σ.symm Eτ : ℕ) := by
                    have hle := numclust_fwd_firstProcessed_le σ _ Rτ hImgne Rτ hatt
                    rw [hEτ]
                    exact hle
                  have hle2 : (σ.symm Eτ : ℕ) ≤ (σ.symm Rτ : ℕ) := by
                    obtain ⟨j, hjS, hym⟩ := Finset.mem_image.mp hEmem
                    obtain ⟨hjnei, hsome⟩ := hSτmem j hjS
                    cases hTj : T j with
                    | none => rw [hTj] at hsome; simp at hsome
                    | some x =>
                      have hl2j : (hl2 j).getD j =
                          (if x ∈ Mτ then some Rτ else some x).getD j := by
                        simp only [hhl2, if_neg hjnei, hTj]
                      by_cases hxM : x ∈ Mτ
                      · have hEE : Eτ = Rτ := by
                          rw [← hym]; beta_reduce; rw [hl2j]; simp [hxM]
                        rw [hEE]
                      · have hxE : x = Eτ := by
                          rw [← hym]; beta_reduce; rw [hl2j]; simp [hxM]
                        rw [← hxE]
                        have hle := hrootle j hjS
                        have hget : (T j).getD j = x := by rw [hTj]; simp
                        rw [hget] at hle
                        rw [hRτRinf]
                        exact hle
                  have hEq : (σ.symm Eτ : ℕ) = (σ.symm Rτ : ℕ) :=
                    le_antisymm hle2 hle1
                  exact σ.symm.injective (Fin.val_injective hEq)
                have hnode : ¬ (Eτ ≠ Rτ ∧ g Rτ - g i < τ) := fun h => h.1 hEτRτ
                have hrMτ' : r ∈ Mτ := by rw [← hlab]; exact hRinfMτ
                have hRτr : Rτ = r := hRτRinf.trans hlab
                simp only [hT'uf, hT'my]
                rw [if_neg hnode]
                beta_reduce
                rw [if_neg hri, hTr_r]
                show (if r ∈ Mτ then some Rτ else some r) = some r
                rw [if_pos hrMτ', hRτr]
              · -- Rinf ∉ Mτ: T' keeps r's old root; the demotion branch also fixes r.
                have hrMτ' : r ∉ Mτ := by
                  intro h; rw [← hlab] at h; exact hRinfMτ h
                have hrRτ : r ≠ Rτ := by
                  intro h; apply hrMτ'; rw [h]; exact hRτmem
                simp only [hT'uf, hT'my]
                by_cases hD : Eτ ≠ Rτ ∧ g Rτ - g i < τ
                · rw [if_pos hD]
                  beta_reduce
                  rw [if_neg hri, hTr_r]
                  show (if (if r ∈ Mτ then some Rτ else some r) = some Rτ then some Eτ
                      else if r ∈ Mτ then some Rτ else some r) = some r
                  rw [if_neg hrMτ', if_neg (by simp [hrRτ])]
                · rw [if_neg hD]
                  beta_reduce
                  rw [if_neg hri, hTr_r]
                  show (if r ∈ Mτ then some Rτ else some r) = some r
                  rw [if_neg hrMτ']
            · -- Case A: no redirect, lab r = some r with r ∉ Minf.
              rw [if_neg haM] at hlab
              simp only [Option.some.injEq] at hlab
              rw [hlab] at hlr haM
              by_cases hrMτ : r ∈ Mτ
              · -- entry-label constancy (hREF): r ∈ Minf — absurd.
                obtain ⟨j, hjS, hjT⟩ := hMτpre r hrMτ
                have hlj : lab j = some r := by
                  have h := hREF j r hjT
                  rw [hlr] at h
                  exact h
                have hrm : r ∈ Minf := by
                  have h1 := hlabjS j hjS
                  have h3 : some ((lab j).getD j) = some r := h1.symm.trans hlj
                  simp only [Option.some.injEq] at h3
                  rw [← h3]
                  exact hrMS j hjS
                exact (haM hrm).elim
              · have hrRτ : r ≠ Rτ := by
                  intro h; apply hrMτ; rw [h]; exact hRτmem
                have hTr_r : T r = some r := hKback r (Or.inl hlr)
                simp only [hT'uf, hT'my]
                by_cases hD : Eτ ≠ Rτ ∧ g Rτ - g i < τ
                · rw [if_pos hD]
                  beta_reduce
                  rw [if_neg hri, hTr_r]
                  show (if (if r ∈ Mτ then some Rτ else some r) = some Rτ then some Eτ
                      else if r ∈ Mτ then some Rτ else some r) = some r
                  rw [if_neg hrMτ, if_neg (by simp [hrRτ])]
                · rw [if_neg hD]
                  beta_reduce
                  rw [if_neg hri, hTr_r]
                  show (if r ∈ Mτ then some Rτ else some r) = some r
                  rw [if_neg hrMτ]
      · -- prominent: prominent dth' r → T' r = some r.
        -- hA4 (at level t+1, k = t) gives (g i : EReal) ≤ dth r, so prominence forces
        -- the merge gap g r − g i ≥ τ both for the new (strict) death and an old death.
        rw [hdth' r] at hprom
        obtain ⟨hgr, hTr_r, hrnei⟩ : (g i + τ : ℝ) ≤ g r ∧ T r = some r ∧ r ≠ i := by
          by_cases hrM : r ∈ numclust_fwd_dying g Dm δ σ lab i
          · -- new (strict) death at level g i; r is a plain root, hence a τ-root.
            rw [if_pos hrM] at hprom
            have hrm : r ∈ Minf :=
              (Finset.mem_erase.mp (Finset.mem_filter.mp hrM).1).2
            refine ⟨?_, hKback r (Or.inl (hMroot r hrm)), ?_⟩
            · have h1 := hprom.2
              rw [← EReal.coe_add] at h1
              exact EReal.coe_le_coe_iff.mp h1
            · intro hri; rw [hri] at hrm; exact hiM hrm
          · -- old death unchanged: prominent dth r; hA4 transports g i ≤ dth r.
            rw [if_neg hrM] at hprom
            refine ⟨?_, hKback r (Or.inr ⟨hprom.1, hprom.2⟩), ?_⟩
            · have hgi : (g i : EReal) ≤ dth r := by
                have h2 := hA4 r hprom.1 ⟨t, ht⟩ (Nat.lt_succ_self t)
                rw [show σ ⟨t, ht⟩ = i from by rw [← hiσ]; exact σ.apply_symm_apply i] at h2
                exact h2
              have h1 : (g i : EReal) + (τ : EReal) ≤ (g r : EReal) :=
                (add_le_add hgi (le_refl (τ : EReal))).trans hprom.2
              rw [← EReal.coe_add] at h1
              exact EReal.coe_le_coe_iff.mp h1
            · intro hri
              have hdthi : dth i = ⊥ := by
                by_contra hc
                have h3 := hDlab i hc
                rw [hlabi] at h3
                simp at h3
              rw [hri] at hprom
              exact hprom.1 hdthi
        by_cases hrMτ : r ∈ Mτ
        · -- r ∈ Mτ: the gap filter forces r = riτ, and riτ is then the σ-eldest
          -- member of Mτ (every other member has gap < τ, hence strictly smaller g).
          have hrri : r = riτ := by
            rw [hMτ] at hrMτ
            rcases Finset.mem_insert.mp hrMτ with rfl | hfil
            · rfl
            · exfalso
              have hgapm : g r - g i < τ := (Finset.mem_filter.mp hfil).2
              linarith [hgapm, hgr]
          have hgr' : (g i + τ : ℝ) ≤ g riτ := by rw [← hrri]; exact hgr
          have hTr' : T riτ = some riτ := by rw [← hrri]; exact hTr_r
          have hMτmax : ∀ m ∈ Mτ, (σ.symm m : ℕ) ≤ (σ.symm riτ : ℕ) := by
            intro m hm
            rw [hMτ] at hm
            rcases Finset.mem_insert.mp hm with rfl | hfil
            · rfl
            · have hgapm : g m - g i < τ := (Finset.mem_filter.mp hfil).2
              have hgm : g m < g riτ := by linarith [hgapm, hgr']
              by_contra h
              push_neg at h
              have h4 := hmono riτ m (le_of_lt h)
              linarith
          have hRτri : Rτ = riτ := by
            rw [hRτ]
            have hMτne : Mτ.Nonempty := by rw [hMτ]; exact Finset.insert_nonempty _ _
            simp only [firstProcessed, dif_pos hMτne]
            have hrimem : σ.symm riτ ∈ Mτ.image σ.symm :=
              Finset.mem_image.mpr ⟨riτ, Finset.mem_insert_self _ _, rfl⟩
            have hmax : (Mτ.image σ.symm).max' (hMτne.image _) = σ.symm riτ :=
              (Finset.max'_eq_iff (Mτ.image σ.symm) (hMτne.image _) (σ.symm riτ)).mpr
                ⟨hrimem,
                  fun b hb => by
                    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hb
                    exact Fin.le_iff_val_le_val.mpr (hMτmax m hm)⟩
            rw [hmax, σ.apply_symm_apply]
          have hnode : ¬ (Eτ ≠ Rτ ∧ g Rτ - g i < τ) := by
            rintro ⟨h1, h2⟩
            rw [hRτri] at h2
            linarith [hgr']
          rw [hrri]
          simp only [hT'uf, hT'my]
          rw [if_neg hnode]
          beta_reduce
          have hriM : riτ ∈ Mτ := Finset.mem_insert_self _ _
          rw [if_neg (hMτroot riτ hriM).2, hTr']
          show (if riτ ∈ Mτ then some Rτ else some riτ) = some riτ
          rw [if_pos hriM, hRτri]
        · -- r ∉ Mτ: T' r keeps r's old root in both demotion branches.
          have hrRτ : r ≠ Rτ := by
            intro h; apply hrMτ; rw [h]; exact hRτmem
          simp only [hT'uf, hT'my]
          by_cases hD : Eτ ≠ Rτ ∧ g Rτ - g i < τ
          · rw [if_pos hD]
            beta_reduce
            rw [if_neg hrnei, hTr_r]
            show (if (if r ∈ Mτ then some Rτ else some r) = some Rτ then some Eτ
                else if r ∈ Mτ then some Rτ else some r) = some r
            rw [if_neg hrMτ, if_neg (by simp [hrRτ])]
          · rw [if_neg hD]
            beta_reduce
            rw [if_neg hrnei, hTr_r]
            show (if r ∈ Mτ then some Rτ else some r) = some r
            rw [if_neg hrMτ]
    · -- Kfwd: τ-root ⇒ plain-root ∨ prominent-after (Hroots case tree).
      --
      -- CONSUMER TRACE (att36): the ONLY downstream consumer of conjunct 5 is
      -- `numclust_fwd_R_char` (reads `hCI.2.2.2.2.1`, line ~2405) with
      -- `rcases hKfwd with hl | ⟨h1,h2⟩`, i.e. it needs EXACTLY the 2-case
      -- prominence form `lab r = some r ∨ (dth r ≠ ⊥ ∧ dth r + τ ≤ g r)`; R_char
      -- then feeds `numclust_fwd_M_region`/`M_rank` and the assembly. (NR, conjunct 8,
      -- is the other consumer.) So Kfwd's form is constrained by R_char's statement.
      --
      -- OBSTRUCTION (subtlety #2, mission-confirmed — DO NOT retry prominence / the
      -- reverse's real-death form): this file's `numclust_fwd_deathStep` records only
      -- STRICT deaths (`numclust_fwd_dying = (M.erase R).filter (g i < g r)`), unlike
      -- the reverse's all-merge `jointStep`. Two tie/gap remainders therefore survive
      -- as τ-roots while failing BOTH candidate forms:
      --   (a) tie-saddle: `r = Rτ ≠ R = Rinf` with `g i = g r` and `Eτ = Rτ` (no
      --       demotion) ⟹ `T' r = some r`; if `r ∈ Minf` then `lab' r = Rinf ≠ r` and
      --       `dth' r = dth r = ⊥` (the tie is not recorded). Reachable: IsSortOrder's
      --       tie-breaking permits `g i = g r` with r σ-earlier (hmono only gives
      --       `g r ≥ g i`). Here lab'≠some r AND dth'=⊥ — prominence and real-death both fail.
      --   (b) small-gap winner: `r = Rτ = riτ` (the insert head, not τ-filtered) with a
      --       strict death `g i < g r` but gap `g r − g i < τ` ⟹ `dth' r = g i` with
      --       `g i + τ > g r` (a real death that is NOT prominent) and `lab' r ≠ r`.
      -- RECOMMENDED FORM: the per-step CI must carry a weaker remainder case, e.g.
      --   `lab' r = some r ∨ (dth' r ≠ ⊥ ∧ dth' r + τ ≤ g r)
      --      ∨ (lab' r ≠ some r ∧ ¬(dth' r ≠ ⊥ ∧ dth' r + τ ≤ g r))`
      -- (the last disjunct absorbing (a)&(b)); R_char, evaluated only at threshold 0,
      -- must then recover the 2-case prominence form for FINAL roots. The FINAL
      -- characterization (immortal ∨ prominence) is validated (~4M cases), so the
      -- remainder is EMPTY at t=0 (the tie/gap-τ τ-entry is re-merged or dies before the
      -- end); closing R_char needs either an added "no remainder survivor" CI conjunct
      -- evaluated at 0, or a direct monotonicity/elder-rule argument that the remainder
      -- cannot be a final root. (The 4th "catch-all" disjunct makes the form a tautology,
      -- so the informative content lives entirely in the empty-at-0 fact.)
      -- ORCH FOREGROUND SKELETON (03:35Z), after three analysis-phase deaths
      -- (att38/39/40): the bridges below are transcribed verbatim from the PROVEN
      -- Kback bullet (same context shape); then the case tree with named branches.
      -- att39's simulation (1.17M cases, ZERO violations) says the 2-case form holds
      -- for EVERY surviving root — the branch proofs find the structural reason.
      intro r hTr
      set Rinf := numclust_fwd_R Dm δ σ lab i with hRinfdef
      set Minf := numclust_fwd_M Dm δ σ lab i with hMinfdef
      have hlab'uf : ∀ w, (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1 w =
          (if w = i then some Rinf
            else match lab w with
              | some a => if a ∈ Minf then some Rinf else some a
              | none => none) := by
        intro w
        rw [numclust_fwd_deathStep_lab_ne g Dm δ σ lab dth i hS]
      have hdth' : ∀ w, (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).2 w =
          (if w ∈ numclust_fwd_dying g Dm δ σ lab i then ((g i : EReal)) else dth w) := by
        intro w
        rw [numclust_fwd_deathStep_snd n g Dm δ σ lab dth i, if_neg hS]
      have hSτne : Sτ.Nonempty := by rw [hSτ]; exact Finset.nonempty_iff_ne_empty.mpr hST
      have hSτmem : ∀ j ∈ Sτ, j ≠ i ∧ (T j).isSome = true := by
        intro j hj; rw [hSτ] at hj
        exact ⟨(Finset.mem_filter.mp hj).2.1, (Finset.mem_filter.mp hj).2.2.2⟩
      have hjSlab : ∀ j ∈ Sτ, j ∈ numclust_fwd_S Dm δ lab i := by
        intro j hj; rw [hSeq] at hj; exact hj
      have hlabjS : ∀ j ∈ Sτ, lab j = some ((lab j).getD j) :=
        fun j hj => numclust_fwd_S_root Dm δ lab i j (hjSlab j hj)
      have hrMS : ∀ j ∈ Sτ, (lab j).getD j ∈ Minf := by
        intro j hj; rw [hMinfdef]
        exact (numclust_fwd_mem_M Dm δ σ lab i _).mpr (Or.inr ⟨j, hjSlab j hj, rfl⟩)
      have hMroot : ∀ s : Fin n, s ∈ Minf → lab s = some s :=
        fun s hs => numclust_fwd_M_root Dm δ σ lab i hS hI2 s hs
      have hMne : Minf.Nonempty := by rw [hMinfdef]; exact Finset.insert_nonempty _ _
      have hRinfmem : Rinf ∈ Minf :=
        numclust_fwd_fp_mem n σ Minf
          (numclust_fwd_root lab (firstProcessed σ (numclust_fwd_S Dm δ lab i) i)) hMne
      have hRinfroot : lab Rinf = some Rinf := hMroot Rinf hRinfmem
      have hiM : i ∉ Minf := by
        rw [hMinfdef]; intro h
        have hSne : (numclust_fwd_S Dm δ lab i).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hS
        rcases (numclust_fwd_mem_M Dm δ σ lab i i).mp h with heq | ⟨j, hjS, hrj⟩
        · have hfp := numclust_fwd_fp_mem n σ (numclust_fwd_S Dm δ lab i) i hSne
          have hlabfp := numclust_fwd_S_root Dm δ lab i _ hfp
          have heq' : i = (lab (firstProcessed σ (numclust_fwd_S Dm δ lab i) i)).getD
              (firstProcessed σ (numclust_fwd_S Dm δ lab i) i) := heq
          rw [← heq'] at hlabfp
          exact absurd (hI2 _ _ hlabfp) (by rw [hlabi]; simp)
        · have hlabj := numclust_fwd_S_root Dm δ lab i j hjS
          have hrj' : (lab j).getD j = i := hrj
          rw [hrj'] at hlabj
          exact absurd (hI2 _ _ hlabj) (by rw [hlabi]; simp)
      have hMτroot : ∀ m ∈ Mτ, T m = some m ∧ m ≠ i := by
        intro m hm
        rw [hMτ] at hm
        rcases Finset.mem_insert.mp hm with rfl | hm'
        · obtain ⟨_, hsome⟩ :=
            hSτmem _ (by rw [hSτ]; exact numclust_fwd_fp_mem n σ _ i hSτne)
          cases hTf : T (firstProcessed σ Sτ i) with
          | none => rw [hTf] at hsome; simp at hsome
          | some s =>
            have hri : riτ = s := by rw [hriτ, hTf]; simp
            refine ⟨?_, ?_⟩
            · rw [hri]; exact hA2 _ _ hTf
            · rw [hri]; intro hsi; rw [hsi] at hTf
              exact absurd (hA2 _ _ hTf) (by rw [hTi]; simp)
        · have him := (Finset.mem_filter.mp hm').1
          obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp him
          obtain ⟨_, hsome⟩ := hSτmem j hjS
          cases hTj : T j with
          | none => rw [hTj] at hsome; simp at hsome
          | some s =>
            have hget : (T j).getD j = s := by rw [hTj]; simp
            rw [hget] at hjm
            rw [← hjm]
            refine ⟨?_, ?_⟩
            · exact hA2 _ _ hTj
            · intro hsi; rw [hsi] at hTj
              exact absurd (hA2 _ _ hTj) (by rw [hTi]; simp)
      have hRτmem : Rτ ∈ Mτ := by
        rw [hRτ]
        exact numclust_fwd_fp_mem n σ _ _ (by rw [hMτ]; exact Finset.insert_nonempty _ _)
      have hRτroot : T Rτ = some Rτ := (hMτroot Rτ hRτmem).1
      have hRτnei : Rτ ≠ i := (hMτroot Rτ hRτmem).2
      -- THE GAP FACT (named; prove FIRST — the transport workhorse): every
      -- plain-merged member OUTSIDE the τ-filter has gap ≥ τ. (It enters Minf
      -- only via the S-image or as the plain head; the heads coincide with riτ
      -- — which IS in Mτ as the insert head — so s ∉ Mτ excludes the head; the
      -- filter excludes gap-≥τ members. Head coincidence: for j ∈ Sτ, its
      -- T-root x satisfies lab j = lab x (hREF) with x self-labeled in Minf
      -- (hrMS + hMroot), so the plain head (lab j).getD j = x = riτ's source.)
      -- THE T-IMAGE GAP FACT (airtight — pure filter semantics; prove EARLY):
      --   a T-image member outside Mτ was excluded by the gap filter, so gap ≥ τ.
      have hgapti : ∀ s ∈ Sτ.image (fun j => (T j).getD j), s ∉ Mτ →
          (g i + τ : ℝ) ≤ g s := by
        intro s hs hout
        obtain ⟨j, hjS, rfl⟩ := Finset.mem_image.mp hs
        -- the T-image membership hs survives the rfl; a gap < τ would put
        -- (T j).getD j in the τ-filter, hence in Mτ — contradicting hout.
        by_contra hc
        push_neg at hc
        exact hout (by
          rw [hMτ]
          exact Finset.mem_insert_of_mem
            (Finset.mem_filter.mpr ⟨hs, by linarith⟩))
      -- ORCH NOTE (after a deeper orchestrator pass): the FULL hgap
      --   (∀ s ∈ Minf, s ∉ Mτ → gap ≥ τ) has TWO subtle cases — the plain-HEAD
      --   case (the label-head can differ from riτ when the τ-split separates
      --   them: a δ-neighbor's LABEL-root need not be its T-root) and the
      --   separate-τ-entry case (a τ-root inside a merged plain family whose
      --   τ-entry never joined the τ-merge — its gap is NOT constrained by
      --   the filter directly). att39's 1.17M-case simulation found ZERO
      --   per-step violations, so every violating configuration is unreachable
      --   — the N3 dying-transport must resolve the residual case either via
      --   hgapti (when r is in the T-image), the r = Rinf self-label
      --   resolution, or an ordering/CI-ELD mechanism. TIMEBOX the deep chase;
      --   bank partials.
      have hgap : ∀ s ∈ Minf, s ∉ Mτ → (g i + τ : ℝ) ≤ g s := by
        intro s hs hout
        rw [hMinfdef] at hs
        -- plain witness: a δ-neighbour w (S-side) with lab w = some s
        -- (Minf head or S-image; both give an S-member labelled by s)
        have hSne : (numclust_fwd_S Dm δ lab i).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hS
        have hfpS : firstProcessed σ (numclust_fwd_S Dm δ lab i) i ∈
            numclust_fwd_S Dm δ lab i := numclust_fwd_fp_mem n σ _ i hSne
        have hwit : ∃ w ∈ numclust_fwd_S Dm δ lab i, lab w = some s := by
          rcases (numclust_fwd_mem_M Dm δ σ lab i s).mp hs with hhd | ⟨j, hjS, hrj⟩
          · refine ⟨firstProcessed σ (numclust_fwd_S Dm δ lab i) i, hfpS, ?_⟩
            have hhd' : s = (lab (firstProcessed σ (numclust_fwd_S Dm δ lab i) i)).getD
                (firstProcessed σ (numclust_fwd_S Dm δ lab i) i) := hhd
            have hlab := numclust_fwd_S_root Dm δ lab i _ hfpS
            rw [← hhd'] at hlab
            exact hlab
          · refine ⟨j, hjS, ?_⟩
            have hrj' : (lab j).getD j = s := hrj
            have hlab := numclust_fwd_S_root Dm δ lab i j hjS
            rw [hrj'] at hlab
            exact hlab
        obtain ⟨w, hwS, hwl⟩ := hwit
        -- w is also τ-side; let x be its T-root; REF pins lab x = some s
        have hwSτ : w ∈ Sτ := by rw [hSeq]; exact hwS
        obtain ⟨_, hwsome⟩ := hSτmem w hwSτ
        cases hTw : T w with
        | none => rw [hTw] at hwsome; simp at hwsome
        | some x =>
          have hlx : lab x = some s := by rw [← hREF w x hTw]; exact hwl
          rcases hKfwd x (hA2 w x hTw) with hself | ⟨hdthx, hprom⟩
          · -- x = s: s is a T-image member; hgapti delivers the gap
            have hxs : x = s := by
              rw [hself] at hlx
              simp only [Option.some.injEq] at hlx
              exact hlx
            have hget : (T w).getD w = s := by rw [hTw, hxs]; simp
            exact hgapti s (Finset.mem_image.mpr ⟨w, hwSτ, hget⟩) hout
          · -- x ≠ s: x is a prominent dead root; A4 + hEl + hmono lift the gap to s
            have hA4x : (g i : EReal) ≤ dth x := by
              have h2 := hA4 x hdthx ⟨t, ht⟩ (Nat.lt_succ_self t)
              rw [show σ ⟨t, ht⟩ = i from by rw [← hiσ]; exact σ.apply_symm_apply i] at h2
              exact h2
            have h1 : (g i + τ : ℝ) ≤ g x := by
              have hle : (g i : EReal) + (τ : EReal) ≤ (g x : EReal) :=
                (add_le_add hA4x (le_refl (τ : EReal))).trans hprom
              rw [← EReal.coe_add] at hle
              exact EReal.coe_le_coe_iff.mp hle
            exact h1.trans (hmono x s (hEl x s hlx))
      -- THE CONTAINMENT FACT (named; prove SECOND): Mτ's members are plain members.
      -- NOTE (att42): the FULL hMτsub (∀ m ∈ Mτ, m ∈ Minf) is FALSE — a prominent
      -- dead `fp = riτ` head (T fp = some fp, lab fp ≠ some fp, dth fp ≠ ⊥, g fp ≥ g i + τ)
      -- is FCI-consistent (Kfwd-at-fp allows prominence; Kback-at-fp is trivial since
      -- T fp = some fp) yet riτ = fp ∉ Minf (Minf members are self-labelled). So Mτ ⊄ Minf.
      -- The branches below do NOT use hMτsub: N2 derives Rτ ∈ Minf directly from the
      -- self-labelled case (Kfwd-old at Rτ: lab Rτ = some Rτ → witness j with T j = some
      -- Rτ and REF → (lab j).getD j = Rτ ∈ Minf), and the prominent case transports dth.
      by_cases hD : Eτ ≠ Rτ ∧ g Rτ - g i < τ
      · -- E-MERGE: T' w = if redirect w = some Rτ then some Eτ else redirect w.
        --   Surviving roots: Eτ (the re-root target) + the untouched old roots
        --   (Rτ itself is re-rooted to Eτ — it does NOT survive).
        by_cases hri : r = i
        · -- (E1) IMPOSSIBLE: redirect i = some Rτ, so T' i = some Eτ with Eτ ≠ i
          --   (Eτ is a firstProcessed over OLD roots: its source set is the
          --   Sτ-image of (T ·).getD's — all ≠ i by hMτroot-style ordering).
          have hEτnei : Eτ ≠ i := by
            by_cases himg : (Sτ.image (fun j => (hl2 j).getD j)).Nonempty
            · have hEmem : Eτ ∈ Sτ.image (fun j => (hl2 j).getD j) := by
                rw [hEτ]; exact numclust_fwd_fp_mem n σ _ Rτ himg
              obtain ⟨j, hjS, hym⟩ := Finset.mem_image.mp hEmem
              have hjnei : j ≠ i := (hSτmem j hjS).1
              have hwsome : (T j).isSome = true := (hSτmem j hjS).2
              cases hTj : T j with
              | none => rw [hTj] at hwsome; simp at hwsome
              | some x =>
                have hl2j : (hl2 j).getD j =
                    (if x ∈ Mτ then some Rτ else some x).getD j := by
                  simp only [hhl2, if_neg hjnei, hTj]
                by_cases hxM : x ∈ Mτ
                · have hER : Eτ = Rτ := by
                    rw [← hym]; beta_reduce; rw [hl2j]; simp [hxM]
                  intro hEi
                  exact hRτnei (hER.symm.trans hEi)
                · have hEx : x = Eτ := by
                    rw [← hym]; beta_reduce; rw [hl2j]; simp [hxM]
                  intro hEi
                  have hxi : x = i := hEx.trans hEi
                  rw [hxi] at hTj
                  have hbad := hA2 j i hTj
                  rw [hTi] at hbad
                  simp at hbad
            · intro hEi
              have hEq : Eτ = Rτ := by
                simp only [hEτ, firstProcessed, dif_neg himg]
              exact hRτnei (hEq.symm.trans hEi)
          rw [hri] at hTr
          simp only [hT'uf, hT'my] at hTr
          rw [if_pos hD] at hTr
          beta_reduce at hTr
          rw [if_pos rfl] at hTr
          rw [if_pos rfl] at hTr
          simp only [Option.some.injEq] at hTr
          exact absurd hTr hEτnei
        · -- (E2) r ≠ i, surviving. Sub-split: r = Eτ, or redirect r = some r
          --   (an untouched old root — SAME transport as (N3) below).
          --   For r = Eτ (the re-root target): Eτ ≠ Rτ (hD.1) forces the hl2-image
          --   nonempty, so Eτ has a witness j ∈ Sτ with (hl2 j).getD j = Eτ; its
          --   T-root x cannot be in Mτ (else Eτ = Rτ, contra hD.1), so x = Eτ and
          --   Eτ is BOTH a T-image member outside Mτ (⇒ hgapti gap: g i + τ ≤ g Eτ)
          --   and a τ-root (T Eτ = some Eτ via hA2). Kfwd-at-Eτ then closes:
          --   self-label ⇒ lab' Eτ = some Eτ ∨ (Eτ ∈ Minf ∧ Eτ ≠ Rinf ⇒ strict
          --   death re-dated at g i, gap = prominence); old prominence ⇒ transport
          --   (dying: re-date at g i + the hgapti gap; non-dying: dth' = dth).
          simp only [hT'uf, hT'my] at hTr
          rw [if_pos hD] at hTr
          beta_reduce at hTr
          rw [if_neg hri] at hTr
          cases hTrx : T r with
          | none => rw [hTrx] at hTr; simp at hTr
          | some x =>
            rw [hTrx] at hTr
            change (if (if x ∈ Mτ then some Rτ else some x) = some Rτ then some Eτ
                else if x ∈ Mτ then some Rτ else some x) = some r at hTr
            by_cases hxM : x ∈ Mτ
            · -- (E2a) redirect r = some Rτ ⇒ T' r = some Eτ ⇒ r = Eτ.
              rw [if_pos hxM] at hTr
              rw [if_pos rfl] at hTr
              simp only [Option.some.injEq] at hTr
              -- hTr : Eτ = r — rewrite the goal to the Eτ form.
              rw [← hTr]
              -- Eτ's structure: nonempty hl2-image ⇒ witness j ⇒ T j = some Eτ,
              -- Eτ ∉ Mτ, hence the T-image gap (hgapti) and T Eτ = some Eτ (hA2).
              have hImgne : (Sτ.image (fun j => (hl2 j).getD j)).Nonempty := by
                by_contra himg
                exact hD.1 (by simp only [hEτ, firstProcessed, dif_neg himg])
              have hEmem : Eτ ∈ Sτ.image (fun j => (hl2 j).getD j) := by
                rw [hEτ]; exact numclust_fwd_fp_mem n σ _ Rτ hImgne
              obtain ⟨j, hjS, hym⟩ := Finset.mem_image.mp hEmem
              obtain ⟨hjn, hjs⟩ := hSτmem j hjS
              cases hTjE : T j with
              | none => rw [hTjE] at hjs; simp at hjs
              | some x₀ =>
                have hl2j : (hl2 j).getD j =
                    (if x₀ ∈ Mτ then some Rτ else some x₀).getD j := by
                  simp only [hhl2, if_neg hjn, hTjE]
                by_cases hx₀M : x₀ ∈ Mτ
                · have hER : Eτ = Rτ := by
                    rw [← hym]; beta_reduce; rw [hl2j]; simp [hx₀M]
                  exact absurd hER hD.1
                · have hx₀E : x₀ = Eτ := by
                    rw [← hym]; beta_reduce; rw [hl2j]; simp [hx₀M]
                  have hTjEτ : T j = some Eτ := by rw [hTjE, hx₀E]
                  have hTEτ : T Eτ = some Eτ := hA2 j Eτ hTjEτ
                  have hEτnei : Eτ ≠ i := by
                    intro h; rw [h] at hTEτ; rw [hTi] at hTEτ; simp at hTEτ
                  have hEτnotM : Eτ ∉ Mτ := by rw [← hx₀E]; exact hx₀M
                  have hEτTimg : Eτ ∈ Sτ.image (fun j => (T j).getD j) := by
                    refine Finset.mem_image.mpr ⟨j, hjS, ?_⟩
                    rw [hTjEτ]; simp
                  have hgapE : (g i + τ : ℝ) ≤ g Eτ := hgapti Eτ hEτTimg hEτnotM
                  rcases hKfwd Eτ hTEτ with hlabE | ⟨hdtE, hpromE⟩
                  · -- (i) lab Eτ = some Eτ: split on Eτ ∈ Minf.
                    have hlab'Eτ : (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1 Eτ =
                        (if Eτ ∈ Minf then some Rinf else some Eτ) := by
                      simp only [hlab'uf Eτ, if_neg hEτnei, hlabE]
                    by_cases hEτMinf : Eτ ∈ Minf
                    · by_cases hERinf : Eτ = Rinf
                      · left; rw [hlab'Eτ, if_pos hEτMinf, hERinf]
                      · -- Eτ ∈ Minf, Eτ ≠ Rinf: strict death re-dated at g i;
                        -- the hgapti gap is the prominence.
                        right
                        have hltR : g i < g Eτ := by linarith
                        have hlt : (g i : EReal) < (g Eτ : EReal) :=
                          EReal.coe_lt_coe_iff.mpr hltR
                        have hrd : Eτ ∈ numclust_fwd_dying g Dm δ σ lab i :=
                          Finset.mem_filter.mpr
                            ⟨Finset.mem_erase.mpr ⟨hERinf, hEτMinf⟩, hlt⟩
                        rw [hdth' Eτ, if_pos hrd]
                        refine ⟨by simp, ?_⟩
                        have hco : ((g i + τ : ℝ) : EReal) ≤ (g Eτ : EReal) :=
                          EReal.coe_le_coe_iff.mpr hgapE
                        rw [EReal.coe_add] at hco
                        exact hco
                    · left; rw [hlab'Eτ, if_neg hEτMinf]
                  · -- (ii) old prominence at Eτ: transport / re-date via the gap.
                    by_cases hrd : Eτ ∈ numclust_fwd_dying g Dm δ σ lab i
                    · right
                      rw [hdth' Eτ, if_pos hrd]
                      refine ⟨by simp, ?_⟩
                      have hco : ((g i + τ : ℝ) : EReal) ≤ (g Eτ : EReal) :=
                        EReal.coe_le_coe_iff.mpr hgapE
                      rw [EReal.coe_add] at hco
                      exact hco
                    · rw [hdth' Eτ, if_neg hrd]
                      exact Or.inr ⟨hdtE, hpromE⟩
            · -- (E2b) redirect r = some x with x ∉ Mτ ⇒ x = r: an untouched old
              --   root; the N3 transport verbatim (hgap prominence / dth-transport).
              rw [if_neg hxM] at hTr
              have hxR : x ≠ Rτ := fun h => hxM (h ▸ hRτmem)
              have hcond : ¬ (some x = some Rτ) := by
                intro hc; injection hc with h; exact hxR h
              rw [if_neg hcond] at hTr
              simp only [Option.some.injEq] at hTr
              have hTrr : T r = some r := by rw [hTrx, hTr]
              have hrMτ : r ∉ Mτ := by rw [← hTr]; exact hxM
              rcases hKfwd r hTrr with hlabr | ⟨hdt, hprom⟩
              · have hlab'r : (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1 r =
                    (if r ∈ Minf then some Rinf else some r) := by
                  simp only [hlab'uf r, if_neg hri, hlabr]
                by_cases hrMinf : r ∈ Minf
                · by_cases hRinfeq : r = Rinf
                  · left; rw [hlab'r, if_pos hrMinf, hRinfeq]
                  · right
                    have hgr : (g i + τ : ℝ) ≤ g r := hgap r hrMinf hrMτ
                    have hltR : g i < g r := by linarith
                    have hlt : (g i : EReal) < (g r : EReal) :=
                      EReal.coe_lt_coe_iff.mpr hltR
                    have hrd : r ∈ numclust_fwd_dying g Dm δ σ lab i :=
                      Finset.mem_filter.mpr
                        ⟨Finset.mem_erase.mpr ⟨hRinfeq, hrMinf⟩, hlt⟩
                    rw [hdth' r, if_pos hrd]
                    refine ⟨by simp, ?_⟩
                    have hco : ((g i + τ : ℝ) : EReal) ≤ (g r : EReal) :=
                      EReal.coe_le_coe_iff.mpr hgr
                    rw [EReal.coe_add] at hco
                    exact hco
                · left; rw [hlab'r, if_neg hrMinf]
              · by_cases hrd : r ∈ numclust_fwd_dying g Dm δ σ lab i
                · right
                  have hrMinf : r ∈ Minf :=
                    (Finset.mem_erase.mp (Finset.mem_filter.mp hrd).1).2
                  have hgr : (g i + τ : ℝ) ≤ g r := hgap r hrMinf hrMτ
                  rw [hdth' r, if_pos hrd]
                  refine ⟨by simp, ?_⟩
                  have hco : ((g i + τ : ℝ) : EReal) ≤ (g r : EReal) :=
                    EReal.coe_le_coe_iff.mpr hgr
                  rw [EReal.coe_add] at hco
                  exact hco
                · rw [hdth' r, if_neg hrd]
                  exact Or.inr ⟨hdt, hprom⟩
      · -- NO E-MERGE: T' w = redirect w.
        by_cases hri : r = i
        · -- (N1) IMPOSSIBLE: T' i = some Rτ ≠ some i (hRτnei).
          simp only [hT'uf, hT'my] at hTr
          rw [if_neg hD] at hTr
          beta_reduce at hTr
          rw [if_pos hri] at hTr
          rw [hri] at hTr
          simp only [Option.some.injEq] at hTr
          exact absurd hTr hRτnei
        · by_cases hrMτ : r ∈ Mτ
          · -- (N2) r ∈ Mτ surviving ⇒ r = Rτ (every other Mτ member redirects
            --   to some Rτ; self-survival needs redirect r = some r, i.e. r = Rτ).
            --   Rτ's 2-case form: Rτ ∈ Minf (hMτsub) ⇒ lab' Rτ = some Rinf.
            --   EITHER Rinf ∈ Mτ ⇒ Rτ = Rinf (the Kback Case-B chain) ⇒ self ✓,
            --   OR Rτ ≠ Rinf ⇒ Rτ ∈ dying (strict: g i < g Rτ — Rτ ≠ the entry's
            --   σ-eldest Rinf, via hmono/CI-ELD) ⇒ dth' Rτ = g i. The gap:
            --   ¬hD gives Eτ = Rτ ∨ g Rτ - g i ≥ τ. The g Rτ - g i ≥ τ case is
            --   prominence ✓. The Eτ = Rτ case (gap possibly < τ) is the LAST
            --   sub-case: Eτ = Rτ makes Rτ the σ-eldest of the hl2-image; chase
            --   Rinf ∈ the hl2-image ⇒ Rτ = Rinf ⇒ contradiction with Rτ ≠ Rinf
            --   ⇒ done. The σ-eldest + firstProcessed_le + CI-ELD chains close it.
            -- N2 reduction: the surviving Mτ member must be the merge target.
            have hrRτ : r = Rτ := by
              simp only [hT'uf, hT'my] at hTr
              rw [if_neg hD] at hTr
              beta_reduce at hTr
              rw [if_neg hri] at hTr
              have hTrr : T r = some r := (hMτroot r hrMτ).1
              rw [hTrr] at hTr
              change (if r ∈ Mτ then some Rτ else some r) = some r at hTr
              rw [if_pos hrMτ] at hTr
              simp only [Option.some.injEq] at hTr
              exact hTr.symm
            rw [hrRτ]
            by_cases hRτM : Rτ ∈ Minf
            · -- N2a: Rτ ∈ Minf — lab' Rτ = some Rinf — the Rinf-chase.
              by_cases hRinfMτ : Rinf ∈ Mτ
              · -- N2a1: Rinf ∈ Mτ ⇒ Rτ = Rinf (the Kback Case-B chain) ⇒ self.
                -- every Mτ member is the T-root of an Sτ member (τ-side of hMτpre).
                have hMτpre : ∀ m ∈ Mτ, ∃ j ∈ Sτ, T j = some m := by
                  intro m hm
                  rw [hMτ] at hm
                  rcases Finset.mem_insert.mp hm with rfl | hm'
                  · refine ⟨firstProcessed σ Sτ i, numclust_fwd_fp_mem n σ _ i hSτne, ?_⟩
                    have hsome : (T (firstProcessed σ Sτ i)).isSome = true :=
                      (hSτmem _ (numclust_fwd_fp_mem n σ _ i hSτne)).2
                    cases hTf : T (firstProcessed σ Sτ i) with
                    | none => rw [hTf] at hsome; simp at hsome
                    | some s =>
                      have hri : riτ = s := by rw [hriτ, hTf]; simp
                      rw [hri]
                  · have him := (Finset.mem_filter.mp hm').1
                    obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp him
                    have hsome : (T j).isSome = true := (hSτmem j hjS).2
                    cases hTj : T j with
                    | none => rw [hTj] at hsome; simp at hsome
                    | some s =>
                      have hget : (T j).getD j = s := by rw [hTj]; simp
                      have hms : m = s := hjm.symm.trans hget
                      refine ⟨j, hjS, ?_⟩
                      rw [hms]; exact hTj
                have hRinfEldest : ∀ s ∈ Minf, (σ.symm s : ℕ) ≤ (σ.symm Rinf : ℕ) := by
                  intro s hs
                  have hle := numclust_fwd_firstProcessed_le σ Minf
                    (numclust_fwd_root lab (firstProcessed σ (numclust_fwd_S Dm δ lab i) i))
                    hMne s hs
                  rw [hRinfdef]
                  exact hle
                have hrootle : ∀ j ∈ Sτ,
                    (σ.symm ((T j).getD j) : ℕ) ≤ (σ.symm Rinf : ℕ) := by
                  intro j hjS
                  have hls : lab j = some ((lab j).getD j) := hlabjS j hjS
                  have hpjM : (lab j).getD j ∈ Minf := hrMS j hjS
                  have hiso : (T j).isSome = true := (hSτmem j hjS).2
                  cases hTj : T j with
                  | none => rw [hTj] at hiso; simp at hiso
                  | some s =>
                    have hlm : lab s = some ((lab j).getD j) := by
                      rw [← hREF j s hTj]; exact hls
                    have hle1 : (σ.symm s : ℕ) ≤ (σ.symm ((lab j).getD j) : ℕ) :=
                      hEl s _ hlm
                    show (σ.symm s : ℕ) ≤ (σ.symm Rinf : ℕ)
                    exact hle1.trans (hRinfEldest _ hpjM)
                have hMτle : ∀ m ∈ Mτ, (σ.symm m : ℕ) ≤ (σ.symm Rinf : ℕ) := by
                  intro m hm
                  obtain ⟨j, hjS, hjT⟩ := hMτpre m hm
                  have hle := hrootle j hjS
                  have hget : (T j).getD j = m := by rw [hjT]; simp
                  rw [hget] at hle
                  exact hle
                have hRτRinf : Rτ = Rinf := by
                  rw [hRτ]
                  have hne : Mτ.Nonempty := by rw [hMτ]; exact Finset.insert_nonempty _ _
                  simp only [firstProcessed, dif_pos hne]
                  have hrimem : σ.symm Rinf ∈ Mτ.image σ.symm :=
                    Finset.mem_image.mpr ⟨Rinf, hRinfMτ, rfl⟩
                  have hmax : (Mτ.image σ.symm).max' (hne.image _) = σ.symm Rinf :=
                    (Finset.max'_eq_iff (Mτ.image σ.symm) (hne.image _) (σ.symm Rinf)).mpr
                      ⟨hrimem,
                        fun b hb => by
                          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hb
                          exact Fin.le_iff_val_le_val.mpr (hMτle m hm)⟩
                  rw [hmax, σ.apply_symm_apply]
                left
                have hlab'Rτ : (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1 Rτ =
                    (if Rτ ∈ Minf then some Rinf else some Rτ) := by
                  simp only [hlab'uf Rτ, if_neg hRτnei, hMroot Rτ hRτM]
                rw [hlab'Rτ, if_pos hRτM, ← hRτRinf]
              · -- N2a2: Rinf ∉ Mτ — tie/strict split on the death.
                -- MASTER GAP LEMMA: (g i + τ) ≤ g Rτ. If Eτ ≠ Rτ, ¬hD forces it; if
                -- Eτ = Rτ, the collapse chase: any unredirected Sτ T-root (Case A)
                -- promotes via hgapti + the Eτ-order; else (Case B) Rinf's plain
                -- witness sends its T-root into Mτ — either into Minf (⇒ Rinf = it,
                -- contradicting Rinf ∉ Mτ) or a prominent dead head whose A4-
                -- transported g i ≤ dth + the Mτ σ-order gives the gap again.
                have hgapfull : (g i + τ : ℝ) ≤ g Rτ := by
                  by_cases hEq : Eτ = Rτ
                  · -- Eτ = Rτ: the collapse chase.
                    have hImgne : (Sτ.image (fun j => (hl2 j).getD j)).Nonempty :=
                      hSτne.image _
                    have hMτne2 : Mτ.Nonempty := by
                      rw [hMτ]; exact Finset.insert_nonempty _ _
                    have hMτbound : ∀ m ∈ Mτ, (σ.symm m : ℕ) ≤ (σ.symm Rτ : ℕ) := by
                      intro m hm
                      have hle := numclust_fwd_firstProcessed_le σ Mτ riτ hMτne2 m hm
                      rw [hRτ]
                      exact hle
                    by_cases hCaseA : ∃ j ∈ Sτ, (T j).getD j ∉ Mτ
                    · -- Case A: an unredirected Sτ T-root — hgapti + the Eτ-order.
                      obtain ⟨j, hjS, hjnot⟩ := hCaseA
                      obtain ⟨hjn, hjs⟩ := hSτmem j hjS
                      cases hTj : T j with
                      | none => rw [hTj] at hjs; simp at hjs
                      | some x =>
                        have hget : (T j).getD j = x := by rw [hTj]; simp
                        have hxnotM : ¬ (x ∈ Mτ) := by
                          intro hm
                          exact hjnot (by rw [hget]; exact hm)
                        have hgapA : (g i + τ : ℝ) ≤ g x :=
                          hgapti x (Finset.mem_image.mpr ⟨j, hjS, hget⟩) hxnotM
                        have hlin2 : x ∈ Sτ.image (fun j => (hl2 j).getD j) :=
                          Finset.mem_image.mpr ⟨j, hjS, by
                            simp only [hhl2, if_neg hjn, hTj]
                            rw [if_neg hxnotM]
                            simp⟩
                        have hleE : (σ.symm x : ℕ) ≤ (σ.symm Eτ : ℕ) := by
                          have hle := numclust_fwd_firstProcessed_le σ
                            (Sτ.image (fun j => (hl2 j).getD j)) Rτ hImgne x hlin2
                          rw [hEτ]
                          exact hle
                        have hmonoA : g x ≤ g Rτ := hmono x Rτ (hEq ▸ hleE)
                        linarith
                    · -- Case B: every Sτ T-root ∈ Mτ — Rinf's plain witness chases in.
                      push_neg at hCaseA
                      have hfpS : firstProcessed σ (numclust_fwd_S Dm δ lab i) i ∈
                          numclust_fwd_S Dm δ lab i := numclust_fwd_fp_mem n σ _ i
                          (Finset.nonempty_iff_ne_empty.mpr hS)
                      have hwit : ∃ j₀ ∈ numclust_fwd_S Dm δ lab i,
                          (lab j₀).getD j₀ = Rinf := by
                        rcases (numclust_fwd_mem_M Dm δ σ lab i Rinf).mp hRinfmem
                          with hhd | ⟨j, hjS', hrj⟩
                        · exact ⟨firstProcessed σ (numclust_fwd_S Dm δ lab i) i,
                            hfpS, hhd.symm⟩
                        · exact ⟨j, hjS', hrj⟩
                      obtain ⟨j₀, hj₀S, hj₀get⟩ := hwit
                      have hj₀τ : j₀ ∈ Sτ := by rw [hSeq]; exact hj₀S
                      obtain ⟨hj₀n, hwis⟩ := hSτmem j₀ hj₀τ
                      cases hTj₀ : T j₀ with
                      | none => rw [hTj₀] at hwis; simp at hwis
                      | some x₀ =>
                        have hget₀ : (T j₀).getD j₀ = x₀ := by rw [hTj₀]; simp
                        have hx₀M : x₀ ∈ Mτ := by
                          rw [← hget₀]; exact hCaseA j₀ hj₀τ
                        have hj₀lab : lab j₀ = some Rinf := by
                          have hl₀ := hlabjS j₀ hj₀τ
                          rw [hj₀get] at hl₀
                          exact hl₀
                        have hx₀lab : lab x₀ = some Rinf :=
                          (hREF j₀ x₀ hTj₀).symm.trans hj₀lab
                        by_cases hx₀i : x₀ ∈ Minf
                        · exfalso
                          have hxl : lab x₀ = some x₀ := hMroot x₀ hx₀i
                          have hxR : x₀ = Rinf := by
                            rw [hxl] at hx₀lab
                            simp only [Option.some.injEq] at hx₀lab
                            exact hx₀lab
                          exact hRinfMτ (by rw [← hxR]; exact hx₀M)
                        · have hTroot : T x₀ = some x₀ := (hMτroot x₀ hx₀M).1
                          rcases hKfwd x₀ hTroot with hself | ⟨hd₀, hp₀⟩
                          · exfalso
                            rw [hself] at hx₀lab
                            simp only [Option.some.injEq] at hx₀lab
                            exact hRinfMτ (by rw [← hx₀lab]; exact hx₀M)
                          · have hA4x₀ : (g i : EReal) ≤ dth x₀ := by
                              have h2 := hA4 x₀ hd₀ ⟨t, ht⟩ (Nat.lt_succ_self t)
                              rw [show σ ⟨t, ht⟩ = i from by rw [← hiσ]; exact σ.apply_symm_apply i] at h2
                              exact h2
                            have h1 : (g i : EReal) + (τ : EReal) ≤ (g x₀ : EReal) :=
                              (add_le_add hA4x₀ (le_refl (τ : EReal))).trans hp₀
                            rw [← EReal.coe_add] at h1
                            have hcox : (g i + τ : ℝ) ≤ g x₀ :=
                              EReal.coe_le_coe_iff.mp h1
                            have hmon : g x₀ ≤ g Rτ := hmono x₀ Rτ (hMτbound x₀ hx₀M)
                            linarith
                  · -- Eτ ≠ Rτ: ¬hD forces the gap directly.
                    by_contra hc
                    push_neg at hc
                    have hc2 : g Rτ - g i < τ := by linarith
                    exact hD ⟨hEq, hc2⟩
                have hRne : Rτ ≠ Rinf := fun h =>
                  hRinfMτ (by rw [← h]; exact hRτmem)
                by_cases hstrict : (g i : ℝ) < g Rτ
                · -- N2a2s: strict — Rτ ∈ dying ⇒ dth' Rτ = g i; hgapfull is prominence.
                  right
                  have hlt : (g i : EReal) < (g Rτ : EReal) :=
                    EReal.coe_lt_coe_iff.mpr hstrict
                  have hrd : Rτ ∈ numclust_fwd_dying g Dm δ σ lab i :=
                    Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hRne, hRτM⟩, hlt⟩
                  rw [hdth' Rτ, if_pos hrd]
                  refine ⟨by simp, ?_⟩
                  have hco : ((g i + τ : ℝ) : EReal) ≤ (g Rτ : EReal) :=
                    EReal.coe_le_coe_iff.mpr hgapfull
                  rw [EReal.coe_add] at hco
                  exact hco
                · -- N2a2t: tie — dth' Rτ = dth Rτ = ⊥ (NR-core); hgapfull + tie kills it.
                  exfalso
                  have hle0 : (g i : ℝ) ≤ g Rτ := by
                    have hge := (hI0 Rτ).mp (by rw [hMroot Rτ hRτM]; simp)
                    have hp : (σ.symm i : ℕ) ≤ (σ.symm Rτ : ℕ) := by
                      rw [hSymmI]; omega
                    exact hmono i Rτ hp
                  have hge2 : g Rτ ≤ g i := le_of_not_gt hstrict
                  linarith
            · -- N2b: Rτ ∉ Minf — the direct label chase (self ∨ the redirect).
              rcases hKfwd Rτ hRτroot with hlabr | ⟨hdt, hprom⟩
              · -- Kfwd self-label: lab' Rτ = some Rτ directly (Rτ ∉ Minf).
                left
                have hlab'Rτ : (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1 Rτ =
                    (if Rτ ∈ Minf then some Rinf else some Rτ) := by
                  simp only [hlab'uf Rτ, if_neg hRτnei, hlabr]
                rw [hlab'Rτ, if_neg hRτM]
              · -- old prominence: Rτ ∉ Minf ⇒ not a dying root ⇒ dth' = dth; transport.
                right
                have hrd : Rτ ∉ numclust_fwd_dying g Dm δ σ lab i := by
                  intro h
                  exact hRτM (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).2
                rw [hdth' Rτ, if_neg hrd]
                exact ⟨hdt, hprom⟩
          · -- (N3) r ∉ Mτ: untouched old root; hgap + dying membership close both cases.
            -- Step 1: reduce T' r = some r to T r = some r (value ∉ Mτ).
            simp only [hT'uf, hT'my] at hTr
            rw [if_neg hD] at hTr
            beta_reduce at hTr
            rw [if_neg hri] at hTr
            cases hTrx : T r with
            | none => rw [hTrx] at hTr; simp at hTr
            | some x =>
              rw [hTrx] at hTr
              change (if x ∈ Mτ then some Rτ else some x) = some r at hTr
              by_cases hxM : x ∈ Mτ
              · rw [if_pos hxM] at hTr
                simp only [Option.some.injEq] at hTr
                have hrm : r ∈ Mτ := by rw [← hTr]; exact hRτmem
                exact absurd hrm hrMτ
              · rw [if_neg hxM] at hTr
                simp only [Option.some.injEq] at hTr
                have hTrr : T r = some r := by rw [hTrx, hTr]
                rcases hKfwd r hTrr with hlabr | ⟨hdt, hprom⟩
                · -- (a) lab r = some r: split on r ∈ Minf (hgap re-dates ties)
                  have hlab'r : (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1 r =
                      (if r ∈ Minf then some Rinf else some r) := by
                    simp only [hlab'uf r, if_neg hri, hlabr]
                  by_cases hrMinf : r ∈ Minf
                  · by_cases hRinfeq : r = Rinf
                    · -- lab' r = some Rinf = some r
                      left
                      rw [hlab'r, if_pos hrMinf, hRinfeq]
                    · -- r ∈ Minf, r ≠ Rinf: strict death (hgap ⇒ g i < g r) + prominence
                      right
                      have hgr : (g i + τ : ℝ) ≤ g r := hgap r hrMinf hrMτ
                      have hltR : g i < g r := by linarith
                      have hlt : (g i : EReal) < (g r : EReal) :=
                        EReal.coe_lt_coe_iff.mpr hltR
                      have hrd : r ∈ numclust_fwd_dying g Dm δ σ lab i :=
                        Finset.mem_filter.mpr
                          ⟨Finset.mem_erase.mpr ⟨hRinfeq, hrMinf⟩, hlt⟩
                      rw [hdth' r, if_pos hrd]
                      refine ⟨by simp, ?_⟩
                      have hco : ((g i + τ : ℝ) : EReal) ≤ (g r : EReal) :=
                        EReal.coe_le_coe_iff.mpr hgr
                      rw [EReal.coe_add] at hco
                      exact hco
                  · -- r ∉ Minf: lab' r = some r
                    left
                    rw [hlab'r, if_neg hrMinf]
                · -- (b) old prominence: re-date at g i (hgap) or transport
                  by_cases hrd : r ∈ numclust_fwd_dying g Dm δ σ lab i
                  · right
                    have hrMinf : r ∈ Minf :=
                      (Finset.mem_erase.mp (Finset.mem_filter.mp hrd).1).2
                    have hgr : (g i + τ : ℝ) ≤ g r := hgap r hrMinf hrMτ
                    rw [hdth' r, if_pos hrd]
                    refine ⟨by simp, ?_⟩
                    have hco : ((g i + τ : ℝ) : EReal) ≤ (g r : EReal) :=
                      EReal.coe_le_coe_iff.mpr hgr
                    rw [EReal.coe_add] at hco
                    exact hco
                  · rw [hdth' r, if_neg hrd]
                    exact Or.inr ⟨hdt, hprom⟩
    · -- SPLIT: re-scoped (att37) to the trivial form — see the FCI def comment.
      -- Consumer trace: conjunct 6 has NO downstream consumer (no `.2.2.2.2.2.1`
      -- accessor anywhere; R_char reads only Kfwd `.2.2.2.2.1` and NR
      -- `.2.2.2.2.2.2.2.1`), so any true maintainable form suffices; the trivial
      -- form absorbs both strict-death remainders (tie-saddle: `lab' r ≠ some r`
      -- with `dth' r = ⊥`; small-gap winner: real but non-prominent `dth' r`).
      intro r h
      trivial
    · -- A4: recorded deaths dominate all future (lower-position) levels
      intro r hr k hk
      have hdthform : (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).2 r =
          (if r ∈ numclust_fwd_dying g Dm δ σ lab i then ((g i : EReal)) else dth r) := by
        rw [numclust_fwd_deathStep_snd n g Dm δ σ lab dth i, if_neg hS]
      by_cases hrd : r ∈ numclust_fwd_dying g Dm δ σ lab i
      · rw [hdthform, if_pos hrd] at hr
        rw [hdthform, if_pos hrd]
        have hgi : (g (σ k) : EReal) ≤ (g i : EReal) := by
          have hle : (σ.symm (σ k) : ℕ) ≤ (σ.symm i : ℕ) := by
            rw [σ.symm_apply_apply, hSymmI]; omega
          exact_mod_cast hmono (σ k) i hle
        exact hgi
      · rw [hdthform, if_neg hrd] at hr
        rw [hdthform, if_neg hrd]
        exact hA4 r hr k (by omega)
    · -- NR: dead roots are not current plain roots — whole-step, via InvCore_step
      exact (numclust_fwd_InvCore_step g Dm δ σ t ht i hiσ lab dth
        ⟨hI0, hI2, hNRcore, hDlab⟩).2.2.1
    · -- CI-ELD: the plain entry's root stays σ-eldest through the τ/plain merge.
      -- Ported from the reverse lane's CI-ELD merge site (match-form lab').
      intro v r h
      set Rinf := numclust_fwd_R Dm δ σ lab i with hRinfdef
      set Minf := numclust_fwd_M Dm δ σ lab i with hMinfdef
      have hlab'uf : ∀ w, (numclust_fwd_deathStep n g Dm δ σ (lab, dth) i).1 w =
          (if w = i then some Rinf
            else match lab w with
              | some a => if a ∈ Minf then some Rinf else some a
              | none => none) := by
        intro w
        rw [numclust_fwd_deathStep_lab_ne g Dm δ σ lab dth i hS]
      rw [hlab'uf v] at h
      have hMroot : ∀ s : Fin n, s ∈ Minf → lab s = some s :=
        fun s hs => numclust_fwd_M_root Dm δ σ lab i hS hI2 s hs
      have hMne : Minf.Nonempty := by rw [hMinfdef]; exact Finset.insert_nonempty _ _
      have hRinfmem : Rinf ∈ Minf :=
        numclust_fwd_fp_mem n σ Minf
          (numclust_fwd_root lab (firstProcessed σ (numclust_fwd_S Dm δ lab i) i)) hMne
      have hRinfroot : lab Rinf = some Rinf := hMroot Rinf hRinfmem
      have hRinfEldest : ∀ s ∈ Minf, (σ.symm s : ℕ) ≤ (σ.symm Rinf : ℕ) := by
        intro s hs
        have hle := numclust_fwd_firstProcessed_le σ Minf
          (numclust_fwd_root lab (firstProcessed σ (numclust_fwd_S Dm δ lab i) i)) hMne s hs
        rw [hRinfdef]
        exact hle
      by_cases hvi : v = i
      · -- v = i: `lab' i = some Rinf`, so `r = Rinf`; `i` is σ-younger than `Rinf`
        -- (an old root: `lab Rinf = some Rinf` ⟹ `t+1 ≤ σ.symm Rinf` via `hI0`).
        rw [hvi, if_pos rfl] at h
        simp only [Option.some.injEq] at h
        rw [hvi, ← h]
        have hsome : (lab Rinf).isSome = true := by rw [hRinfroot]; simp
        have hge := (hI0 Rinf).mp hsome
        rw [hSymmI]
        omega
      · -- v ≠ i: split on the old label; the redirect either sends `v` to `Rinf`
        -- (merged, `hEl` + eldest) or leaves it (unmerged, `hEl` directly).
        rw [if_neg hvi] at h
        cases hlv : lab v with
        | none => rw [hlv] at h; simp at h
        | some a =>
          rw [hlv] at h
          change (if a ∈ Minf then some Rinf else some a) = some r at h
          by_cases haM : a ∈ Minf
          · rw [if_pos haM] at h
            simp only [Option.some.injEq] at h
            rw [← h]
            have hvel : (σ.symm v : ℕ) ≤ (σ.symm a : ℕ) := hEl v a hlv
            have hael : (σ.symm a : ℕ) ≤ (σ.symm Rinf : ℕ) := hRinfEldest a haM
            omega
          · rw [if_neg haM] at h
            simp only [Option.some.injEq] at h
            rw [← h]
            exact hEl v a hlv

/-- The full coupled run satisfies the coupling invariant at threshold `0`
(fold-lift of `numclust_fwd_cstep_CIs`, reusing the file's `_ufStep_rooted_fold` /
`barStep_rooted_fold` idiom for the plain-sweep invariant core). -/
private theorem numclust_fwd_cRun_CI (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    numclust_fwd_FCI g τ σ 0
      (numclust_fwd_cRun n g Dm δ τ σ).1
      (numclust_fwd_cRun n g Dm δ τ σ).2.1
      (numclust_fwd_cRun n g Dm δ τ σ).2.2 := by
  have key : ∀ j : ℕ, j ≤ n → numclust_fwd_FCI g τ σ (n - j)
      ((((List.finRange n).reverse).take j).foldl
          (fun st k => numclust_fwd_cstep n g Dm δ τ σ st (σ k))
          ((fun _ => none), (fun _ => none), (fun _ => ⊥))).1
      ((((List.finRange n).reverse).take j).foldl
          (fun st k => numclust_fwd_cstep n g Dm δ τ σ st (σ k))
          ((fun _ => none), (fun _ => none), (fun _ => ⊥))).2.1
      ((((List.finRange n).reverse).take j).foldl
          (fun st k => numclust_fwd_cstep n g Dm δ τ σ st (σ k))
          ((fun _ => none), (fun _ => none), (fun _ => ⊥))).2.2 := by
    intro j hj
    induction j with
    | zero =>
      simp only [List.take_zero, List.foldl_nil]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro v; simp
      · intro v r h; simp at h
      · intro v r h; simp at h
      · intro r h
        rcases h with h | ⟨h1, h2⟩
        · simp at h
        · simp at h1
      · intro r h; simp at h
      · intro r h; simp at h
      · intro r hr; exact absurd rfl hr
      · intro r hr; exact absurd rfl hr
      · intro v r h; simp at h
    | succ j ih =>
      have hjn : j < n := by omega
      have hlen : List.length (List.finRange n).reverse = n := by
        rw [List.length_reverse, List.length_finRange]
      have hinst : j < (List.finRange n).reverse.length := by rw [hlen]; omega
      rw [List.take_succ_eq_append_getElem hinst]
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hfin : ((List.finRange n).reverse)[j]'hinst = ⟨n - (j + 1), by omega⟩ := by
        rw [List.getElem_reverse hinst]
        rw [List.getElem_finRange (by rw [List.length_finRange]; omega)]
        exact Fin.val_injective (by simp [List.length_finRange, Fin.val_cast]; omega)
      rw [hfin]
      have hcore := numclust_fwd_InvCore_fold n g Dm δ σ j (by omega)
      have hproj2 := numclust_fwd_cRun_snd (n := n) g Dm δ τ σ
        ((List.finRange n).reverse.take j)
        ((fun _ => none), (fun _ => none), (fun _ => ⊥))
      have hInv : numclust_fwd_InvCore g σ (n - (j + 1) + 1)
          (((List.finRange n).reverse.take j).foldl
            (fun st k => numclust_fwd_cstep n g Dm δ τ σ st (σ k))
            ((fun _ => none), (fun _ => none), (fun _ => ⊥))).2.1
          (((List.finRange n).reverse.take j).foldl
            (fun st k => numclust_fwd_cstep n g Dm δ τ σ st (σ k))
            ((fun _ => none), (fun _ => none), (fun _ => ⊥))).2.2 := by
        rw [show n - (j + 1) + 1 = n - j by omega]
        rw [congrArg Prod.fst hproj2, congrArg Prod.snd hproj2]
        exact hcore
      exact numclust_fwd_cstep_CIs g Dm hDm hDm0 δ τ hδ hτ σ hσ (n - (j + 1)) (by omega)
        (σ ⟨n - (j + 1), by omega⟩) (σ.symm_apply_apply _) _ _ _
        (by simpa only [show n - (j + 1) + 1 = n - j by omega] using ih (by omega))
        hInv
  have hfinal : List.take n (List.finRange n).reverse = (List.finRange n).reverse := by
    apply List.take_of_length_le
    rw [List.length_reverse, List.length_finRange]
  simpa only [numclust_fwd_cRun, hfinal, Nat.sub_self] using key n (Nat.le_refl n)

/-! ### (R) characterization of the final τ-roots via the private death map -/

/-- Every final τ-root is, in the plain (τ = +∞) sweep, either an immortal plain root
(fixed point with `barDeath r = ⊥`) or died a strict death whose prominence is at
least `τ`.  Only the forward direction is asserted: the converse fails (e.g. for an
immortal plain root `r` with `g r < τ`). -/
private theorem numclust_fwd_R_char (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    ∀ r : Fin n, r ∈ numclust_fwd_rootFinset n g Dm δ τ σ →
      ((barRun g Dm δ σ).1 r = some r ∧ numclust_fwd_barDeath n g Dm δ σ r = ⊥) ∨
        (numclust_fwd_barDeath n g Dm δ σ r ≠ ⊥ ∧
          (numclust_fwd_barDeath n g Dm δ σ r) + (τ : EReal) ≤ (g r : EReal)) := by
  -- Roadmap (see also /tmp/opencode/agents/numclust_fwd_explanation.md):
  -- τ-death rule: a neighbour root r dies in the τ-sweep at step i iff
  --   (g r − g i < τ) ∧ (r ≠ R_plain(i))  (with E = R_plain: after the first merge
  --   the `E`-winner of the second merge equals the plain winner).
  -- Structural invariant: the τ-partition refines the plain partition and the plain
  -- root of every plain entry is a τ-root; both preserved step-by-step (the τ merge
  -- is a sub-merge of the plain merge).
  -- (→) if r is a final τ-root then in the plain sweep r never absorbed-prominently:
  --     if PlainRoot r then barDeath r = ⊥; else its first plain death i₀ satisfies
  --     g r − g i₀ ≥ τ (else it would have τ-survived i₀ since g is non-increasing
  --     along the sweep), giving barDeath r + τ ≤ g r.
  -- (←) converse per the τ-death rule.
  -- Tie subtlety: a plain merge with g i = g r records no death yet kills the plain
  -- root — such r is ri, whose τ-merge fires via the E-merge, hence NOT a final
  -- τ-root; this is why the ⊥-branch needs PlainRoot r.
  -- Final derivation from the coupled-run coupling invariant: evaluate
  -- `numclust_fwd_cRun_CI` at threshold 0 (at t = 0 every vertex is τ-labelled, so
  -- `Kfwd` applies to the τ-root `r`), and read `lab`/`dth` off `cRun_proj` +
  -- `BD_states_eq` + the definition of `barDeath`.  The `⊥` in the left branch comes
  -- from the NR component (a current plain root is never dead).
  intro r hr
  have hCI := numclust_fwd_cRun_CI n g Dm hDm hDm0 δ τ hδ hτ σ hσ
  have hproj := numclust_fwd_cRun_proj n g Dm δ τ σ
  have hBD := numclust_fwd_BD_states_eq n g Dm δ σ
  obtain ⟨_, hruf, hτr⟩ := Finset.mem_filter.mp hr
  have hTr : (numclust_fwd_cRun n g Dm δ τ σ).1 r = some r := by
    rw [hproj.1]; exact hruf
  have hKfwd := hCI.2.2.2.2.1 r hTr
  have hNR := hCI.2.2.2.2.2.2.2.1
  have hlab : (numclust_fwd_cRun n g Dm δ τ σ).2.1 r = (barRun g Dm δ σ).1 r := by
    rw [congrArg Prod.fst hproj.2, hBD]
  have hdth : (numclust_fwd_cRun n g Dm δ τ σ).2.2 r = numclust_fwd_barDeath n g Dm δ σ r := by
    have h1 : (numclust_fwd_cRun n g Dm δ τ σ).2.2
        = (numclust_fwd_deathRun n g Dm δ σ).2 := congrArg Prod.snd hproj.2
    simp only [h1, numclust_fwd_barDeath]
  rcases hKfwd with hl | ⟨h1, h2⟩
  · refine Or.inl ⟨?_, ?_⟩
    · rw [← hlab]; exact hl
    · by_contra hne
      exact absurd hl (hNR r (by rw [hdth]; exact hne))
  · refine Or.inr ⟨?_, ?_⟩
    · rw [← hdth]; exact h1
    · rw [← hdth]; exact h2

/-! ### (M) region membership and rank-below-multiplicity -/

/-- The barcode point of a final τ-root lies in the region: its death is at least `τ`
below its birth, and its birth is at least `τ`. -/
private theorem numclust_fwd_M_region (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    ∀ r ∈ numclust_fwd_rootFinset n g Dm δ τ σ,
      numclust_fwd_barDeath n g Dm δ σ r ≤ (g r : EReal) - (τ : EReal) ∧
        (τ : EReal) ≤ (g r : EReal) := by
  intros r hr
  obtain ⟨_, hroot⟩ := Finset.mem_filter.mp hr
  -- birth ≥ τ comes straight from the root filter.
  have hg : (τ : EReal) ≤ (g r : EReal) := by exact_mod_cast hroot.2
  refine ⟨?_, hg⟩
  rcases numclust_fwd_R_char n g Dm hDm hDm0 δ τ hδ hτ σ hσ r hr with
    ⟨_, hbot⟩ | ⟨_, hadd⟩
  · -- immortal: death is `⊥`, below everything.
    rw [hbot]; exact bot_le
  · -- died a strict death with death + τ ≤ birth; move τ to the right.
    exact (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot τ))
      (Or.inl (EReal.coe_ne_top τ))).mpr hadd

/-- The rank of a final τ-root is strictly below the barcode multiplicity of its
barcode point. -/
private theorem numclust_fwd_M_rank (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    ∀ r ∈ numclust_fwd_rootFinset n g Dm δ τ σ,
      (numclust_fwd_rank n g Dm δ τ σ r : ℕ∞)
        < ripsBarcode g Dm δ σ (numclust_fwd_barPair n g Dm δ σ r) := by
  intros r hr
  -- strict subset via a single witness not in the smaller set
  have card_lt_witness : ∀ (A B : Finset (Fin n)) (x : Fin n),
      (∀ s ∈ A, s ∈ B) → x ∈ B → x ∉ A → A.card < B.card := by
    intros A B x hsub hxin hxnin
    apply Finset.card_lt_card
    refine ⟨?_, ?_⟩
    · intro s hs; exact hsub s hs
    · intro hcont; exact hxnin (hcont hxin)
  -- the characterization of τ-roots (used to see the rank fiber at `⊥` deaths)
  have hchar := numclust_fwd_R_char n g Dm hDm hDm0 δ τ hδ hτ σ hσ
  rw [numclust_fwd_rank]
  by_cases hdth : numclust_fwd_barDeath n g Dm δ σ r = ⊥
  · -- immortal: the barcode point is `(g r, ⊥)`
    have hp : numclust_fwd_barPair n g Dm δ σ r = ((g r : EReal), ⊥) := by
      rw [numclust_fwd_barPair, hdth]
    rw [hp, numclust_fwd_BD_barcode_immortal n g Dm δ σ ((g r : EReal))]
    -- every member of the rank fiber is an immortal plain root (via R_char:
    -- its death is `⊥`, ruling out the strict-death disjunct).
    have hsub : ∀ s ∈ (numclust_fwd_rootFinset n g Dm δ τ σ).filter
        (fun s => numclust_fwd_barPair n g Dm δ σ s = ((g r : EReal), ⊥) ∧ s < r),
      s ∈ (Finset.univ.filter
        (fun s => (barRun g Dm δ σ).1 s = some s ∧ (g s : EReal) = (g r : EReal))) := by
      intros s hs
      obtain ⟨hsF, hsp, _⟩ := Finset.mem_filter.mp hs
      have hsp' := hsp
      rw [numclust_fwd_barPair] at hsp'
      simp only [Prod.mk.injEq] at hsp'
      obtain ⟨hgs, hds⟩ := hsp'
      rcases hchar s hsF with ⟨hpr, _⟩ | ⟨hnds, _⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, hpr, hgs⟩
      · exact absurd hds hnds
    have hrin : r ∈ (Finset.univ.filter
        (fun s => (barRun g Dm δ σ).1 s = some s ∧ (g s : EReal) = (g r : EReal))) := by
      rcases hchar r hr with ⟨hpr, _⟩ | ⟨hnds, _⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, hpr, rfl⟩
      · exact absurd hdth hnds
    have hrnin : r ∉ (numclust_fwd_rootFinset n g Dm δ τ σ).filter
        (fun s => numclust_fwd_barPair n g Dm δ σ s = ((g r : EReal), ⊥) ∧ s < r) :=
      fun h => absurd ((Finset.mem_filter.mp h).2.2) (lt_irrefl r)
    exact_mod_cast card_lt_witness _ _ r hsub hrin hrnin
  · -- strict death: the multiplicity at the point is exactly the barPair-fiber size.
    have hp2 : (numclust_fwd_barPair n g Dm δ σ r).2 ≠ ⊥ := hdth
    rw [numclust_fwd_BD_barcode_real n g Dm δ σ (numclust_fwd_barPair n g Dm δ σ r) hp2]
    have hsub : ∀ s ∈ (numclust_fwd_rootFinset n g Dm δ τ σ).filter
        (fun s => numclust_fwd_barPair n g Dm δ σ s = numclust_fwd_barPair n g Dm δ σ r ∧ s < r),
      s ∈ (Finset.univ.filter
        (fun s => numclust_fwd_barPair n g Dm δ σ s = numclust_fwd_barPair n g Dm δ σ r)) :=
      fun s hs => Finset.mem_filter.mpr
        ⟨Finset.mem_univ s, (Finset.mem_filter.mp hs).2.1⟩
    have hrin : r ∈ (Finset.univ.filter
        (fun s => numclust_fwd_barPair n g Dm δ σ s = numclust_fwd_barPair n g Dm δ σ r)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ r, rfl⟩
    have hrnin : r ∉ (numclust_fwd_rootFinset n g Dm δ τ σ).filter
        (fun s => numclust_fwd_barPair n g Dm δ σ s = numclust_fwd_barPair n g Dm δ σ r ∧ s < r) :=
      fun h => absurd ((Finset.mem_filter.mp h).2.2) (lt_irrefl r)
    exact_mod_cast card_lt_witness _ _ r hsub hrin hrnin

/-! ### (I) the injection construction into the region copy set -/

/-- The map `r ↦ (barPair r, rank r)` sends final τ-roots into the region copy set. -/
private theorem numclust_fwd_I_map_region (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    ∀ r ∈ numclust_fwd_rootFinset n g Dm δ τ σ,
      numclust_fwd_map n g Dm δ τ σ r ∈ numclust_fwd_regionSet n g Dm δ τ σ := by
  intros r hr
  have hM := numclust_fwd_M_region n g Dm hDm hDm0 δ τ hδ hτ σ hσ r hr
  have hMr := numclust_fwd_M_rank n g Dm hDm hDm0 δ τ hδ hτ σ hσ r hr
  exact ⟨hMr, hM.1, hM.2⟩

/-! ### (J) injectivity of the injection -/

/-- Two final τ-roots with the same barcode point and the same rank are equal. -/
private theorem numclust_fwd_J_inj (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    ∀ r ∈ numclust_fwd_rootFinset n g Dm δ τ σ, ∀ r' ∈ numclust_fwd_rootFinset n g Dm δ τ σ,
      numclust_fwd_map n g Dm δ τ σ r = numclust_fwd_map n g Dm δ τ σ r' → r = r' := by
  -- If a < b share a barcode point, then rank a < rank b: the rank-fiber below b
  -- contains the whole fiber below a plus a itself.
  have inj_helper : ∀ (a b : Fin n),
      a ∈ numclust_fwd_rootFinset n g Dm δ τ σ →
      b ∈ numclust_fwd_rootFinset n g Dm δ τ σ →
      numclust_fwd_barPair n g Dm δ σ a = numclust_fwd_barPair n g Dm δ σ b →
      a < b →
      numclust_fwd_rank n g Dm δ τ σ a < numclust_fwd_rank n g Dm δ τ σ b := by
    intros a b ha hb hpab hab
    rw [numclust_fwd_rank, numclust_fwd_rank, hpab]
    -- both rank-filters are now keyed on `barPair b`; `b`'s fiber ⊇ `a`'s fiber ∪ {a}.
    apply Finset.card_lt_card
    refine ⟨?_, ?_⟩
    · -- the `s < a` fiber is contained in the `s < b` fiber.
      apply Finset.monotone_filter_right
      intro x _ hx
      exact ⟨hx.1, lt_trans hx.2 hab⟩
    · -- `b`'s fiber is not contained in `a`'s: witness `a` (in the former, not the latter).
      intro hcont
      have ha_in : a ∈ (numclust_fwd_rootFinset n g Dm δ τ σ).filter
        (fun s => numclust_fwd_barPair n g Dm δ σ s = numclust_fwd_barPair n g Dm δ σ b ∧ s < b) :=
        Finset.mem_filter.mpr ⟨ha, hpab, hab⟩
      have ha_notin : a ∉ (numclust_fwd_rootFinset n g Dm δ τ σ).filter
        (fun s => numclust_fwd_barPair n g Dm δ σ s = numclust_fwd_barPair n g Dm δ σ b ∧ s < a) :=
        fun h => absurd ((Finset.mem_filter.mp h).2.2) (lt_irrefl a)
      exact ha_notin (hcont ha_in)
  intros r hr r' hr' hmap
  rw [numclust_fwd_map] at hmap
  obtain ⟨hp, hrank⟩ := Prod.mk.inj hmap
  by_contra hne
  rcases Ne.lt_or_gt hne with hrr' | hr'r
  · have := inj_helper r r' hr hr' hp hrr'
    omega
  · have := inj_helper r' r hr' hr hp.symm hr'r
    omega

/-! ### (A) encard/card assembly -/

/-- `numClusters` counts exactly the final τ-roots. -/
private theorem numclust_fwd_A_numclust_card (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) :
    (numClusters g Dm δ τ σ : ℕ∞)
      = ((numclust_fwd_rootFinset n g Dm δ τ σ).card : ℕ∞) := by
  classical
  -- `firstProcessed` returns an element of its (nonempty) set.
  have fp_mem : ∀ (S : Finset (Fin n)) (i₀ : Fin n), S.Nonempty → firstProcessed σ S i₀ ∈ S := by
    intros S i₀ hne
    simp only [firstProcessed, dif_pos hne]
    obtain ⟨s, hs, hsx⟩ :=
      Finset.mem_image.mp (Finset.max'_mem (S.image σ.symm) (hne.image σ.symm))
    rw [← hsx, σ.apply_symm_apply]; exact hs
  -- Abstract lemma: re-pointing the entries with roots in `M` to `R` keeps labels
  -- pointing to fixed points, provided every `m ∈ M` is a root, `R ∈ M`, `lab i = none`,
  -- and `lab` is already rooted.
  have lab2_rooted_abs : ∀ (M : Finset (Fin n)) (R i : Fin n) (lab : UFState n),
      (∀ m ∈ M, lab m = some m) → R ∈ M → lab i = none →
      (∀ v r, lab v = some r → lab r = some r) →
      ∀ x y, (fun v => if v = i then some R else
                 match lab v with
                 | some r => if r ∈ M then some R else some r
                 | none => none) x = some y →
             (fun v => if v = i then some R else
                 match lab v with
                 | some r => if r ∈ M then some R else some r
                 | none => none) y = some y := by
    intros M R i lab hM hRm hni hRt x y hxy
    dsimp only [] at hxy
    by_cases hxi : x = i
    · rw [if_pos hxi] at hxy
      have hEq : R = y := Option.some_inj.mp hxy
      rw [← hEq]
      dsimp only []
      by_cases hRi : R = i
      · rw [if_pos hRi]
      · rw [if_neg hRi, hM R hRm]; dsimp only []; rw [if_pos hRm]
    · rw [if_neg hxi] at hxy
      cases hx : lab x with
      | none => simp [hx] at hxy
      | some r =>
        rw [hx] at hxy
        dsimp only [] at hxy
        by_cases hrm : r ∈ M
        · rw [if_pos hrm] at hxy
          have hEq : R = y := Option.some_inj.mp hxy
          rw [← hEq]
          dsimp only []
          by_cases hRi : R = i
          · rw [if_pos hRi]
          · rw [if_neg hRi, hM R hRm]; dsimp only []; rw [if_pos hRm]
        · rw [if_neg hrm] at hxy
          have hEq : r = y := Option.some_inj.mp hxy
          rw [← hEq]
          dsimp only []
          have hri : r ≠ i := by
            intro hri'
            have h1 : lab i = some r := by rw [← hri']; exact hRt x r hx
            rw [hni] at h1
            exact absurd h1 (by simp)
          rw [if_neg hri, hRt x r hx]
          show (if r ∈ M then some R else some r) = some r
          rw [if_neg hrm]
  -- Abstract lemma: the second merge (re-pointing the `R`-entry to `E`) preserves rootedness.
  have merge_rooted_abs : ∀ (lab2 : UFState n) (E R : Fin n),
      lab2 E = some E → E ≠ R →
      (∀ x y, lab2 x = some y → lab2 y = some y) →
      ∀ x y, (fun v => if lab2 v = some R then some E else lab2 v) x = some y →
             (fun v => if lab2 v = some R then some E else lab2 v) y = some y := by
    intros lab2 E R hE hER hroot x y hxy
    dsimp only [] at hxy
    by_cases hxR : lab2 x = some R
    · rw [if_pos hxR] at hxy
      have hEq : E = y := Option.some_inj.mp hxy
      rw [← hEq]
      dsimp only []
      rw [if_neg (fun h => hER (Option.some_inj.mp (h.symm.trans hE)).symm)]
      exact hE
    · rw [if_neg hxR] at hxy
      have hy : lab2 y = some y := hroot x y hxy
      by_cases hyR : lab2 y = some R
      · have hEq : y = R := Option.some_inj.mp (hy.symm.trans hyR)
        -- impossible: `y = R` would force `lab2 x = some R` via `hxy`.
        rw [hEq] at hxy
        exact absurd hxy hxR
      · dsimp only []; rw [if_neg hyR]; exact hy
  -- Abstract lemma: re-pointing the entries with roots in `M` to `R` keeps the
  -- unprocessed vertex `v` unlabelled.
  have lab2_none_abs : ∀ (M : Finset (Fin n)) (R i v : Fin n) (lab : UFState n),
      v ≠ i → lab v = none →
      (fun w => if w = i then some R else
        match lab w with
        | some r => if r ∈ M then some R else some r
        | none => none) v = none := by
    intros M R i v lab hvi hv
    simp only [if_neg hvi, hv]
  -- Abstract lemma: the second merge keeps an unlabelled vertex unlabelled.
  have merge_none_abs : ∀ (lab2 : UFState n) (E R v : Fin n), lab2 v = none →
      (fun w => if lab2 w = some R then some E else lab2 w) v = none := by
    intros lab2 E R v hv
    simp [hv]
  -- A step never newly labels a vertex other than the processed one.
  have step_preserves_none : ∀ (lab : UFState n) (i v : Fin n), lab v = none → v ≠ i →
      ufStep g Dm δ τ σ lab i v = none := by
    intros lab i v hv hvi
    simp only [ufStep]
    let S : Finset (Fin n) := Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)
    let ri : Fin n := (lab (firstProcessed σ S i)).getD (firstProcessed σ S i)
    let M : Finset (Fin n) :=
      insert ri ((Finset.image (fun j => (lab j).getD j) S).filter (fun r => g r - g i < τ))
    let R : Fin n := firstProcessed σ M ri
    let lab2 : UFState n := fun w => if w = i then some R else
      match lab w with
      | some r => if r ∈ M then some R else some r
      | none => none
    let E : Fin n := firstProcessed σ (Finset.image (fun j => (lab2 j).getD j) S) R
    split_ifs with hS hC
    · rw [Function.update_of_ne hvi (some i) lab]; exact hv
    · exact merge_none_abs lab2 E R v (lab2_none_abs M R i v lab hvi hv)
    · exact lab2_none_abs M R i v lab hvi hv
  -- A step preserves rootedness, given the processed vertex is fresh.
  have step_rooted : ∀ (lab : UFState n) (i : Fin n),
      (∀ v r, lab v = some r → lab r = some r) → lab i = none →
      ∀ v r, ufStep g Dm δ τ σ lab i v = some r → ufStep g Dm δ τ σ lab i r = some r := by
    intros lab i hR hni v r hr
    simp only [ufStep] at hr ⊢
    let S : Finset (Fin n) := Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)
    let ri : Fin n := (lab (firstProcessed σ S i)).getD (firstProcessed σ S i)
    let M : Finset (Fin n) :=
      insert ri ((Finset.image (fun j => (lab j).getD j) S).filter (fun r => g r - g i < τ))
    let R : Fin n := firstProcessed σ M ri
    let lab2 : UFState n := fun w => if w = i then some R else
      match lab w with
      | some r => if r ∈ M then some R else some r
      | none => none
    let E : Fin n := firstProcessed σ (Finset.image (fun j => (lab2 j).getD j) S) R
    split_ifs with hS hC
    · -- i starts a fresh entry rooted at itself.
      rw [if_pos hS] at hr
      by_cases hvi : v = i
      · rw [hvi] at hr
        rw [Function.update_self] at hr
        rw [← Option.some_inj.mp hr]
        rw [Function.update_self]
      · rw [Function.update_of_ne hvi (some i) lab] at hr
        have hvr : lab r = some r := hR v r hr
        by_cases hri : r = i
        · subst hri; exact absurd (hni.symm.trans hvr) (by simp)
        · rw [Function.update_of_ne hri (some i) lab]; exact hvr
    · -- S ≠ ∅, second merge fires: the result is `E`, a lab2-root.
      rw [if_neg hS, if_pos hC] at hr
      have hSne : S.Nonempty := Finset.nonempty_of_ne_empty hS
      have hroot_mem : ∀ j ∈ S, lab ((lab j).getD j) = some ((lab j).getD j) := by
        intros j hj
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hj).2.2.2
        rw [ha]; exact hR j a ha
      have hMroot : ∀ m ∈ M, lab m = some m := by
        intros m hm
        rcases Finset.mem_insert.mp hm with hm' | hm'
        · rw [hm']; exact hroot_mem (firstProcessed σ S i) (fp_mem _ _ hSne)
        · obtain ⟨hm'', _⟩ := Finset.mem_filter.mp hm'
          obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp hm''
          rw [← hjm]; exact hroot_mem j hjS
      have hMne : M.Nonempty := ⟨ri, Finset.mem_insert_self _ _⟩
      have hRm : R ∈ M := fp_mem _ _ hMne
      have hlab2rooted : ∀ x y, lab2 x = some y → lab2 y = some y :=
        lab2_rooted_abs M R i lab hMroot hRm hni hR
      have hEroot : lab2 E = some E := by
        have hSne2 : (Finset.image (fun j => (lab2 j).getD j) S).Nonempty := by
          obtain ⟨j, hj⟩ := hSne
          exact ⟨(lab2 j).getD j, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
        have hEin : E ∈ Finset.image (fun j => (lab2 j).getD j) S := fp_mem _ _ hSne2
        obtain ⟨j, hjS, hjE⟩ := Finset.mem_image.mp hEin
        have hisj : (lab2 j).isSome := by
          have h1 : j ≠ i := (Finset.mem_filter.mp hjS).2.1
          have h2 : (lab j).isSome := (Finset.mem_filter.mp hjS).2.2.2
          show ((if j = i then some R else
            match lab j with
            | some r => if r ∈ M then some R else some r
            | none => none)).isSome
          rw [if_neg h1]
          cases hlab2j : lab j with
          | none => rw [hlab2j] at h2; simp at h2
          | some a => dsimp only []; split <;> exact Option.isSome_some
        have hlab2jE : lab2 j = some E := by
          obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hisj
          have hget : (lab2 j).getD j = a := by rw [ha]; rfl
          have hAE : a = E := hget.symm.trans hjE
          rw [ha, hAE]
        exact hlab2rooted j E hlab2jE
      exact merge_rooted_abs lab2 E R hEroot hC.1 hlab2rooted v r hr
    · -- S ≠ ∅, no second merge: the result is lab2 itself, a rooted map.
      rw [if_neg hS, if_neg hC] at hr
      have hSne : S.Nonempty := Finset.nonempty_of_ne_empty hS
      have hroot_mem : ∀ j ∈ S, lab ((lab j).getD j) = some ((lab j).getD j) := by
        intros j hj
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hj).2.2.2
        rw [ha]; exact hR j a ha
      have hMroot : ∀ m ∈ M, lab m = some m := by
        intros m hm
        rcases Finset.mem_insert.mp hm with hm' | hm'
        · rw [hm']; exact hroot_mem (firstProcessed σ S i) (fp_mem _ _ hSne)
        · obtain ⟨hm'', _⟩ := Finset.mem_filter.mp hm'
          obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp hm''
          rw [← hjm]; exact hroot_mem j hjS
      have hMne : M.Nonempty := ⟨ri, Finset.mem_insert_self _ _⟩
      have hRm : R ∈ M := fp_mem _ _ hMne
      exact lab2_rooted_abs M R i lab hMroot hRm hni hR v r hr
  -- Folding the sweep preserves rootedness: each vertex is processed once (σ
  -- injective, `finRange` distinct), so it is fresh at its step.
  have fold_rooted : ∀ (l : List (Fin n)) (lab : UFState n),
      (∀ v r, lab v = some r → lab r = some r) →
      (∀ k ∈ l, lab (σ k) = none) →
      l.Nodup →
      (∀ v r, (l.foldl (fun lab k => ufStep g Dm δ τ σ lab (σ k)) lab) v = some r →
              (l.foldl (fun lab k => ufStep g Dm δ τ σ lab (σ k)) lab) r = some r) := by
    intro l
    induction l with
    | nil => intro lab hR; exact fun _ _ => hR
    | cons k ks ih =>
      intros lab hR hFresh hND
      obtain ⟨hND', hNDks⟩ := List.nodup_cons.mp hND
      have hFreshK : lab (σ k) = none := hFresh k List.mem_cons_self
      have hR1 := step_rooted lab (σ k) hR hFreshK
      have hFresh1 : ∀ j ∈ ks, ufStep g Dm δ τ σ lab (σ k) (σ j) = none := by
        intros j hj
        apply step_preserves_none lab (σ k) (σ j) (hFresh j (List.mem_cons_of_mem _ hj))
        intro heq
        exact absurd (Equiv.injective σ heq)
          (fun (h : j = k) => hND' (h ▸ hj))
      rw [List.foldl_cons]
      exact ih (ufStep g Dm δ τ σ lab (σ k)) hR1 hFresh1 hNDks
  -- The full sweep is rooted: start from the empty labelling, `finRange` is duplicate-free.
  have hfull : ∀ v r, ufRun g Dm δ τ σ v = some r → ufRun g Dm δ τ σ r = some r := by
    have hR0 : ∀ v r, (((fun _ : Fin n => none) : UFState n) v = some r) →
        (((fun _ : Fin n => none) : UFState n) r = some r) :=
      fun _ _ h => absurd h (by simp)
    have hFresh0 : ∀ k ∈ (List.finRange n).reverse,
        ((fun _ : Fin n => none) : UFState n) (σ k) = none := fun _ _ => rfl
    have hND : ((List.finRange n).reverse).Nodup :=
      List.nodup_reverse.mpr (List.nodup_finRange n)
    exact fold_rooted (List.finRange n).reverse ((fun _ : Fin n => none) : UFState n) hR0 hFresh0 hND
  -- The two counting filters coincide: `∃ v, lab v = some r` ↔ `lab r = some r`.
  have hfilter : ∀ r : Fin n,
      ((∃ v, ufRun g Dm δ τ σ v = some r) ∧ τ ≤ g r) ↔
        (ufRun g Dm δ τ σ r = some r ∧ τ ≤ g r) := by
    intro r
    refine ⟨?_, fun ⟨h1, h2⟩ => ⟨⟨r, h1⟩, h2⟩⟩
    rintro ⟨⟨v, hv⟩, hg⟩
    exact ⟨hfull v r hv, hg⟩
  have heq : numClusters g Dm δ τ σ = (numclust_fwd_rootFinset n g Dm δ τ σ).card := by
    simp only [numClusters, numclust_fwd_rootFinset]
    rw [Finset.filter_congr (fun r _ => hfilter r)]
  exact_mod_cast heq

/-- The final τ-roots inject into the region copy set, so their count is at most
the region's encard. -/
private theorem numclust_fwd_A_card_le (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    ((numclust_fwd_rootFinset n g Dm δ τ σ).card : ℕ∞)
      ≤ (numclust_fwd_regionSet n g Dm δ τ σ).encard := by
  -- `r ↦ (barPair r, rank r)` maps the root Finset into the region copy set
  -- (I) and is injective there (J); an injection bounds card by encard.
  have hinj : Set.InjOn (numclust_fwd_map n g Dm δ τ σ)
      ((numclust_fwd_rootFinset n g Dm δ τ σ) : Set (Fin n)) := by
    intros a ha b hb hab
    exact numclust_fwd_J_inj n g Dm hDm hDm0 δ τ hδ hτ σ hσ a ha b hb hab
  have hmap : Set.MapsTo (numclust_fwd_map n g Dm δ τ σ)
      ((numclust_fwd_rootFinset n g Dm δ τ σ) : Set (Fin n))
      (numclust_fwd_regionSet n g Dm δ τ σ) := by
    intros a ha
    exact numclust_fwd_I_map_region n g Dm hDm hDm0 δ τ hδ hτ σ hσ a ha
  calc ((numclust_fwd_rootFinset n g Dm δ τ σ).card : ℕ∞)
      = ((numclust_fwd_rootFinset n g Dm δ τ σ) : Set (Fin n)).encard := by
          rw [Set.encard_coe_eq_coe_finsetCard]
    _ ≤ (numclust_fwd_regionSet n g Dm δ τ σ).encard :=
          Set.encard_le_encard_of_injOn hmap hinj

/-- Forward inequality: the number of clusters output by the τ-thresholded
union-find Procedure 1 is at most the number of barcode copies of the elder-rule
pairing with prominence at least `τ` and birth at least `τ`. -/
theorem solution
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ)
    (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    (numClusters g Dm δ τ σ : ℕ∞)
      ≤ {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < ripsBarcode g Dm δ σ q.1 ∧
          q.1.2 ≤ q.1.1 - (τ : EReal) ∧ (τ : EReal) ≤ q.1.1}.encard :=
  le_trans (le_of_eq (numclust_fwd_A_numclust_card n g Dm δ τ σ))
    (numclust_fwd_A_card_le n g Dm hDm hDm0 δ τ hδ hτ σ hσ)

end
