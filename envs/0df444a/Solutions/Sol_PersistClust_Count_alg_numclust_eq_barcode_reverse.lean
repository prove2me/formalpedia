-- Prove2me | solution 1 for PersistClust.Count.alg_numclust_eq_barcode_reverse
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-10T01:03:54.952838+00:00
-- url     : https://prove2.me/submissions/d3a51068-8f88-48f6-91a2-9fcd534ba0ee

import Mathlib
import Definitions.Def_PersistClust_Count_Algorithm
import Definitions.Def_PersistClust_Count_AlgBarcode

open PersistClust.Count
open Classical

/-!
# Reverse direction: barcode copies (prominence ≥ τ, birth ≥ τ) ↦ distinct clusters

Every copy `((b, d), k)` of the elder-rule barcode with `d ≤ b − τ` and `τ ≤ b` is
realized by a distinct cluster output by the τ-thresholded union-find Procedure 1.

Strategy (validated on 3.96M exhaustive + 40k random cases):
* `(BD)` a private per-root death map of the plain (`τ = +∞`) elder-rule sweep identifies
  each barcode point with the plain-sweep roots realizing it (off-diagonal: roots dying a
  strict death at that level; immortal: roots alive at the end).
* `(R)` the per-root characterization (Claim K, backward direction): a plain root `r` with
  `τ ≤ g r` survives the τ-sweep iff it is immortal or its recorded death `d` has
  prominence `g r − d ≥ τ`.
* `(E)` for every region point `p`, the fiber of surviving roots realizing `p` is at least
  the barcode multiplicity of `p`.
* `(P)` pairing each region copy `(p, k)` with the k-th surviving root in the fiber of `p`
  gives an injective matching into the surviving roots.
* `(A)` the injection gives `encard ≤ card survRoots = numClusters`.
-/

noncomputable section

/-! ### Helper definitions for the combined plain sweep (label + death map + accumulator) -/

private abbrev numclust_rev_neighSet {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (lab : UFState n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)

private abbrev numclust_rev_rootOf {n : ℕ} (lab : UFState n) (j : Fin n) : Fin n :=
  (lab j).getD j

private abbrev numclust_rev_mergeSet {n : ℕ} (σ : Fin n ≃ Fin n) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (lab : UFState n) (i : Fin n) : Finset (Fin n) :=
  let S := numclust_rev_neighSet Dm δ lab i
  insert ((lab (firstProcessed σ S i)).getD (firstProcessed σ S i))
    (S.image (fun j => (lab j).getD j))

private abbrev numclust_rev_eldestRoot {n : ℕ} (σ : Fin n ≃ Fin n) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (lab : UFState n) (i : Fin n) : Fin n :=
  let S := numclust_rev_neighSet Dm δ lab i
  firstProcessed σ (numclust_rev_mergeSet σ Dm δ lab i)
    ((lab (firstProcessed σ S i)).getD (firstProcessed σ S i))

/-- One step of the combined plain sweep: carries the union-find label map, the private
per-root death map (⊥ = never a root, ⊤ = alive root, real `g i` = died at level `g i`), and
the accumulated off-diagonal multiplicity.  The label evolution is exactly `barStep`'s; the
accumulator update is exactly `barStep`'s (strict off-diagonal deaths only); the death map
additionally records `⊤` at a new peak and the level `g i` for every dying root (diagonal
deaths included, but dropped from the accumulator by the strict filter). -/
private def numclust_rev_jointStep {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n)
    (st : UFState n × (Fin n → EReal) × ((EReal × EReal) → ℕ∞)) (i : Fin n)
    : UFState n × (Fin n → EReal) × ((EReal × EReal) → ℕ∞) :=
  let lab := st.1
  let dth := st.2.1
  let acc := st.2.2
  let S := numclust_rev_neighSet Dm δ lab i
  if hS : S = ∅ then
    (Function.update lab i (some i), Function.update dth i ⊤, acc)
  else
    let M := numclust_rev_mergeSet σ Dm δ lab i
    let R := numclust_rev_eldestRoot σ Dm δ lab i
    let lab2 : UFState n := fun v =>
      if v = i then some R
      else Option.bind (lab v) (fun r => if r ∈ M then some R else some r)
    let dyingAll : Finset (Fin n) := M.erase R
    let dyingStrict : Finset (Fin n) :=
      dyingAll.filter (fun r => (g i : EReal) < (g r : EReal))
    let dth2 : Fin n → EReal := fun r => if r ∈ dyingAll then (g i : EReal) else dth r
    let acc2 : (EReal × EReal) → ℕ∞ := fun p =>
      acc p + dyingStrict.sum (fun r => if p = ((g r : EReal), (g i : EReal)) then 1 else 0)
    (lab2, dth2, acc2)

private def numclust_rev_jointRun (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) : UFState n × (Fin n → EReal) × ((EReal × EReal) → ℕ∞) :=
  (List.finRange n).reverse.foldl
    (fun st k => numclust_rev_jointStep g Dm δ σ st (σ k))
    ((fun _ => none), (fun _ => ⊥), (fun _ => 0))

private def numclust_rev_barDeath (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (r : Fin n) : EReal :=
  (numclust_rev_jointRun n g Dm δ σ).2.1 r

private def numclust_rev_finalLab (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) : UFState n :=
  (numclust_rev_jointRun n g Dm δ σ).1

private def numclust_rev_barPair (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (r : Fin n) : EReal × EReal :=
  let d := numclust_rev_barDeath n g Dm δ σ r
  ((g r : EReal), if d = ⊤ then ⊥ else d)

private def numclust_rev_survRoots (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ τ : ℝ)
    (σ : Fin n ≃ Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun r => (∃ v, ufRun g Dm δ τ σ v = some r) ∧ τ ≤ g r)

private def numclust_rev_regionSet (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ τ : ℝ)
    (σ : Fin n ≃ Fin n) : Set ((EReal × EReal) × ℕ) :=
  {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < ripsBarcode g Dm δ σ q.1 ∧
      q.1.2 ≤ q.1.1 - (τ : EReal) ∧ (τ : EReal) ≤ q.1.1}

/-! ### Projections of the combined sweep onto `barRun` -/

private theorem numclust_rev_jointStep_proj {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (lab : UFState n) (dth : Fin n → EReal)
    (acc : (EReal × EReal) → ℕ∞) (i : Fin n) :
    ((numclust_rev_jointStep g Dm δ σ (lab, dth, acc) i).1,
     (numclust_rev_jointStep g Dm δ σ (lab, dth, acc) i).2.2)
      = barStep g Dm δ σ (lab, acc) i := by
  simp only [numclust_rev_jointStep, numclust_rev_neighSet, numclust_rev_mergeSet,
    numclust_rev_eldestRoot, barStep]
  split_ifs with h0
  · rfl
  · apply Prod.ext
    · funext v
      cases hlab : lab v with
      | none => simp only [hlab, Option.bind_none]
      | some x => simp only [hlab, Option.bind_some]
    · rfl

private theorem numclust_rev_foldl_proj {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (l : List (Fin n))
    (init : UFState n × (Fin n → EReal) × ((EReal × EReal) → ℕ∞)) :
    ((l.foldl (fun st k => numclust_rev_jointStep g Dm δ σ st (σ k)) init).1,
     (l.foldl (fun st k => numclust_rev_jointStep g Dm δ σ st (σ k)) init).2.2)
      = l.foldl (fun st k => barStep g Dm δ σ st (σ k)) (init.1, init.2.2) := by
  induction l generalizing init with
  | nil => rfl
  | cons k ks ih =>
    have h := numclust_rev_jointStep_proj g Dm δ σ init.1 init.2.1 init.2.2 (σ k)
    simp only [List.foldl_cons]
    rw [ih (numclust_rev_jointStep g Dm δ σ init (σ k)), h]

private theorem numclust_rev_jointRun_proj (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) :
    (numclust_rev_finalLab n g Dm δ σ,
     (numclust_rev_jointRun n g Dm δ σ).2.2) = barRun g Dm δ σ := by
  simp only [numclust_rev_finalLab, numclust_rev_jointRun, barRun]
  exact numclust_rev_foldl_proj g Dm δ σ (List.finRange n).reverse
    ((fun _ => none), (fun _ => ⊥), (fun _ => 0))

/-! ### `firstProcessed` membership -/

private theorem numclust_rev_firstProcessed_mem {n : ℕ} (σ : Fin n ≃ Fin n)
    (S : Finset (Fin n)) (i₀ : Fin n) (h : S.Nonempty) :
    firstProcessed σ S i₀ ∈ S := by
  have hm : (S.image σ.symm).max' (h.image _) ∈ S.image σ.symm :=
    Finset.max'_mem _ _
  simp only [Finset.mem_image] at hm
  obtain ⟨a, haS, ha⟩ := hm
  simp only [firstProcessed, dif_pos h]
  have hsa : σ ((S.image σ.symm).max' (h.image _)) = a := by
    rw [← ha, Equiv.apply_symm_apply]
  rw [hsa]
  exact haS

/-- `firstProcessed σ S i₀` is the σ-eldest (max-`σ.symm`) member of `S`. -/
private theorem numclust_rev_firstProcessed_le {n : ℕ} (σ : Fin n ≃ Fin n)
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

/-! ### Combined-sweep invariant -/

private def numclust_rev_isRealDeath (x : EReal) : Prop := x ≠ ⊥ ∧ x ≠ ⊤

private def numclust_rev_deathFilter {n : ℕ} (g : Fin n → ℝ) (dth : Fin n → EReal)
    (p : EReal × EReal) : Finset (Fin n) :=
  Finset.univ.filter (fun r =>
    ∃ d : ℝ, dth r = (d : EReal) ∧ p = ((g r : EReal), (d : EReal)) ∧ (d : EReal) < (g r : EReal))

private def numclust_rev_Inv {n : ℕ} (g : Fin n → ℝ) (σ : Fin n ≃ Fin n) (t : ℕ)
    (lab : UFState n) (dth : Fin n → EReal) (acc : (EReal × EReal) → ℕ∞) : Prop :=
  (∀ v : Fin n, (lab v).isSome = true ↔ t ≤ (σ.symm v : ℕ)) ∧
  (∀ r : Fin n, lab r = some r ↔ dth r = ⊤) ∧
  (∀ v r : Fin n, lab v = some r → lab r = some r) ∧
  (∀ r : Fin n, dth r ≠ ⊥ → (lab r).isSome = true) ∧
  (∀ p : EReal × EReal, acc p = ((numclust_rev_deathFilter g dth p).card : ℕ∞))

private theorem numclust_rev_Inv_init {n : ℕ} (g : Fin n → ℝ) (σ : Fin n ≃ Fin n) :
    numclust_rev_Inv g σ n (fun _ => none) (fun _ => ⊥) (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    have hle : ¬ (n ≤ (σ.symm v : ℕ)) := Nat.not_le.mpr (Fin.is_lt (σ.symm v))
    exact iff_of_false (by simp) hle
  · intro r; simp
  · intro v r h; simp at h
  · intro r h; simp at h
  · intro p
    apply Eq.symm
    apply congrArg
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro r _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨d, hd, -⟩
    exact absurd hd (EReal.bot_ne_coe d)

/-! #### Membership and root lemmas about the merge set -/

private theorem numclust_rev_mem_mergeSet {n : ℕ} (σ : Fin n ≃ Fin n) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (lab : UFState n) (i : Fin n) (r : Fin n) :
    r ∈ numclust_rev_mergeSet σ Dm δ lab i ↔
      r = (lab (firstProcessed σ (numclust_rev_neighSet Dm δ lab i) i)).getD
            (firstProcessed σ (numclust_rev_neighSet Dm δ lab i) i) ∨
      ∃ j ∈ numclust_rev_neighSet Dm δ lab i, (lab j).getD j = r := by
  simp only [numclust_rev_mergeSet, Finset.mem_insert, Finset.mem_image]

private theorem numclust_rev_neigh_root {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (lab : UFState n) (i j : Fin n)
    (hj : j ∈ numclust_rev_neighSet Dm δ lab i) :
    lab j = some ((lab j).getD j) := by
  have hisSome := (Finset.mem_filter.mp hj).2.2
  rcases h : lab j with _ | x
  · simp [Option.isSome, h] at hisSome
  · simp only [h, Option.getD_some]

/-- Every member of the merge set is a current root (assuming `S ≠ ∅`). -/
private theorem numclust_rev_mergeSet_root {n : ℕ} (σ : Fin n ≃ Fin n) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (lab : UFState n) (i : Fin n)
    (hS : numclust_rev_neighSet Dm δ lab i ≠ ∅)
    (hI2 : ∀ v r : Fin n, lab v = some r → lab r = some r)
    (r : Fin n) (hr : r ∈ numclust_rev_mergeSet σ Dm δ lab i) :
    lab r = some r := by
  have hSne : (numclust_rev_neighSet Dm δ lab i).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hS
  rcases (numclust_rev_mem_mergeSet σ Dm δ lab i r).mp hr with heq | ⟨j, hjS, hrj⟩
  · have hfp : firstProcessed σ (numclust_rev_neighSet Dm δ lab i) i ∈
        numclust_rev_neighSet Dm δ lab i :=
      numclust_rev_firstProcessed_mem σ (numclust_rev_neighSet Dm δ lab i) i hSne
    have hlabfp :
        lab (firstProcessed σ (numclust_rev_neighSet Dm δ lab i) i) =
          some ((lab (firstProcessed σ (numclust_rev_neighSet Dm δ lab i) i)).getD (firstProcessed σ (numclust_rev_neighSet Dm δ lab i) i)) :=
      numclust_rev_neigh_root Dm δ lab i _ hfp
    rw [heq]
    exact hI2 _ _ hlabfp
  · have hlabj : lab j = some ((lab j).getD j) :=
      numclust_rev_neigh_root Dm δ lab i j hjS
    rw [← hrj]
    exact hI2 _ _ hlabj

/-- When `S ≠ ∅`, the combined step produces the explicit merge triple. -/
private theorem numclust_rev_jointStep_ne {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (lab : UFState n) (dth : Fin n → EReal)
    (acc : (EReal × EReal) → ℕ∞) (i : Fin n)
    (hS : numclust_rev_neighSet Dm δ lab i ≠ ∅) :
    numclust_rev_jointStep g Dm δ σ (lab, dth, acc) i =
      ((fun v => if v = i then some (numclust_rev_eldestRoot σ Dm δ lab i)
            else Option.bind (lab v)
              (fun r => if r ∈ numclust_rev_mergeSet σ Dm δ lab i then
                  some (numclust_rev_eldestRoot σ Dm δ lab i) else some r)),
       (fun r => if r ∈ (numclust_rev_mergeSet σ Dm δ lab i).erase
            (numclust_rev_eldestRoot σ Dm δ lab i) then (g i : EReal) else dth r),
       (fun p => acc p + (((numclust_rev_mergeSet σ Dm δ lab i).erase
            (numclust_rev_eldestRoot σ Dm δ lab i)).filter
            (fun r => (g i : EReal) < (g r : EReal))).sum
          (fun r => if p = ((g r : EReal), (g i : EReal)) then (1 : ℕ∞) else 0))) := by
  simp only [numclust_rev_jointStep, dif_neg hS]

/-- The label update applied at a dying (rooted, in-`M`) vertex `r`: it becomes `some R`. -/
private theorem numclust_rev_f1_die {n : ℕ} (lab : UFState n) (M : Finset (Fin n)) (R : Fin n)
    (r : Fin n) (hrr : lab r = some r) (hrM : r ∈ M) :
    Option.bind (lab r) (fun r' => if r' ∈ M then some R else some r') = some R := by
  rw [hrr, Option.bind_some, if_pos hrM]

/-- The label update applied at a rooted vertex `r ∉ M`: unchanged. -/
private theorem numclust_rev_f1_fix {n : ℕ} (lab : UFState n) (M : Finset (Fin n)) (R : Fin n)
    (r : Fin n) (hrr : lab r = some r) (hrM : r ∉ M) :
    Option.bind (lab r) (fun r' => if r' ∈ M then some R else some r') = some r := by
  rw [hrr, Option.bind_some, if_neg hrM]

/-- `Option.bind` of a never-`none` function preserves `isSome`. -/
private theorem numclust_rev_bind_isSome {n : ℕ} (o : Option (Fin n)) (f : Fin n → Option (Fin n))
    (hf : ∀ a, (f a).isSome = true) (h : o.isSome = true) : (o.bind f).isSome = true := by
  rcases o with _ | x
  · simp at h
  · simpa using hf x

/-! #### The step preservation (the heart of BD) -/

private theorem numclust_rev_Inv_step {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) (t : ℕ) (ht : t < n)
    (lab : UFState n) (dth : Fin n → EReal) (acc : (EReal × EReal) → ℕ∞)
    (h : numclust_rev_Inv g σ (t+1) lab dth acc) :
    numclust_rev_Inv g σ t
      (numclust_rev_jointStep g Dm δ σ (lab, dth, acc) (σ ⟨t, ht⟩)).1
      (numclust_rev_jointStep g Dm δ σ (lab, dth, acc) (σ ⟨t, ht⟩)).2.1
      (numclust_rev_jointStep g Dm δ σ (lab, dth, acc) (σ ⟨t, ht⟩)).2.2 := by
  obtain ⟨hI0, hI1, hI2, hI4, hI5⟩ := h
  set i := σ ⟨t, ht⟩ with hi
  have hσi : σ.symm i = ⟨t, ht⟩ := by rw [hi]; exact σ.symm_apply_apply ⟨t, ht⟩
  have hnsi : ¬ ((lab i).isSome = true) := by rw [hI0, hσi]; simp
  have hlabi : lab i = none := by
    rcases hl : lab i with _ | x
    · rfl
    · exact absurd (by rw [hl]; simp : (lab i).isSome = true) hnsi
  have hdthi : dth i = ⊥ := by
    by_contra hc
    exact absurd (hI4 i hc) (by rw [hlabi]; simp)
  have hsyminj : ∀ v : Fin n, v ≠ i → (σ.symm v : ℕ) ≠ t := by
    intro v hvi heq
    exact hvi (σ.symm.injective (Fin.val_injective (by rw [hσi]; exact heq)))
  by_cases hS : numclust_rev_neighSet Dm δ lab i = ∅
  · -- peak branch: i becomes a new root.
    simp only [numclust_rev_jointStep, dif_pos hS]
    show numclust_rev_Inv g σ t (Function.update lab i (some i))
      (Function.update dth i ⊤) acc
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v
      by_cases hvi : v = i
      · rw [hvi, Function.update_self]
        exact iff_of_true (by simp) (by rw [hσi])
      · rw [Function.update_of_ne hvi]
        constructor
        · intro his
          have := (hI0 v).mp his
          omega
        · intro hle
          have hcvne : (σ.symm v : ℕ) ≠ t := hsyminj v hvi
          exact (hI0 v).mpr (by omega)
    · intro r
      by_cases hri : r = i
      · rw [hri, Function.update_self, Function.update_self]
        exact iff_of_true rfl rfl
      · rw [Function.update_of_ne hri, Function.update_of_ne hri]
        exact hI1 r
    · intro v r h
      by_cases hvi : v = i
      · rw [hvi, Function.update_self] at h
        rw [Option.some.injEq] at h
        rw [← h, Function.update_self]
      · rw [Function.update_of_ne hvi] at h
        have hlr := hI2 v r h
        by_cases hri : r = i
        · rw [hri] at hlr
          rw [hlr] at hlabi
          exact absurd hlabi (by simp)
        · rw [Function.update_of_ne hri, hlr]
    · intro r hd
      by_cases hri : r = i
      · rw [hri, Function.update_self]; simp
      · rw [Function.update_of_ne hri] at hd
        rw [Function.update_of_ne hri]
        exact hI4 r hd
    · intro p
      have hfe : numclust_rev_deathFilter g (Function.update dth i ⊤) p =
          numclust_rev_deathFilter g dth p := by
        apply Finset.filter_congr
        intro r _
        by_cases hri : r = i
        · rw [hri, Function.update_self]
          constructor
          · rintro ⟨d, hd, -⟩; exact absurd hd (EReal.top_ne_coe d)
          · rw [hdthi]; rintro ⟨d, hd, -⟩; exact absurd hd (EReal.bot_ne_coe d)
        · rw [Function.update_of_ne hri]
      rw [hfe]
      exact hI5 p
  · -- merge branch: neighbouring roots merge into R.
    have hSne : (numclust_rev_neighSet Dm δ lab i).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hS
    have hMroot : ∀ r : Fin n, r ∈ numclust_rev_mergeSet σ Dm δ lab i → lab r = some r :=
      numclust_rev_mergeSet_root σ Dm δ lab i hS hI2
    have hMtop : ∀ r : Fin n, r ∈ numclust_rev_mergeSet σ Dm δ lab i → dth r = ⊤ := by
      intro r hr
      exact (hI1 r).mp (hMroot r hr)
    have hRmem : numclust_rev_eldestRoot σ Dm δ lab i ∈ numclust_rev_mergeSet σ Dm δ lab i := by
      have hMne : (numclust_rev_mergeSet σ Dm δ lab i).Nonempty := Finset.insert_nonempty _ _
      simpa only [numclust_rev_eldestRoot] using
        numclust_rev_firstProcessed_mem σ
          (numclust_rev_mergeSet σ Dm δ lab i)
          ((lab (firstProcessed σ (numclust_rev_neighSet Dm δ lab i) i)).getD (firstProcessed σ (numclust_rev_neighSet Dm δ lab i) i))
          hMne
    have hiM : i ∉ numclust_rev_mergeSet σ Dm δ lab i := by
      intro him
      rcases (numclust_rev_mem_mergeSet σ Dm δ lab i i).mp him with heq | ⟨j, hjS, hrj⟩
      · have hfp := numclust_rev_firstProcessed_mem σ (numclust_rev_neighSet Dm δ lab i) i hSne
        have hlabfp := numclust_rev_neigh_root Dm δ lab i _ hfp
        rw [← heq] at hlabfp
        exact absurd (hI2 _ _ hlabfp) (by rw [hlabi]; simp)
      · have hlabj := numclust_rev_neigh_root Dm δ lab i j hjS
        rw [hrj] at hlabj
        exact absurd (hI2 _ _ hlabj) (by rw [hlabi]; simp)
    set M := numclust_rev_mergeSet σ Dm δ lab i with hM
    set R := numclust_rev_eldestRoot σ Dm δ lab i with hR
    set dA := M.erase R with hdA
    set dS := dA.filter (fun r => (g i : EReal) < (g r : EReal)) with hdS
    have hRne : R ∉ dA := by
      intro h
      rw [hdA] at h
      exact absurd rfl (Finset.mem_erase.mp h).1
    have hRi : R ≠ i := by
      intro h; rw [h] at hRmem; exact hiM hRmem
    have hidA : i ∉ dA := by
      intro h; rw [hdA] at h; exact hiM (Finset.mem_erase.mp h).2
    obtain ⟨f1, hf1⟩ : ∃ f1 : UFState n, ∀ v : Fin n, f1 v =
        (if v = i then some R
         else Option.bind (lab v) (fun r => if r ∈ M then some R else some r)) :=
      ⟨_, fun v => rfl⟩
    obtain ⟨f2, hf2⟩ : ∃ f2 : Fin n → EReal, ∀ r : Fin n, f2 r =
        (if r ∈ dA then (g i : EReal) else dth r) := ⟨_, fun r => rfl⟩
    obtain ⟨f3, hf3⟩ : ∃ f3 : (EReal × EReal) → ℕ∞, ∀ p : EReal × EReal, f3 p =
        (acc p + dS.sum (fun r => if p = ((g r : EReal), (g i : EReal)) then (1 : ℕ∞) else 0)) :=
      ⟨_, fun p => rfl⟩
    have htriple : numclust_rev_jointStep g Dm δ σ (lab, dth, acc) i = (f1, f2, f3) := by
      rw [numclust_rev_jointStep_ne g Dm δ σ lab dth acc i hS, ← hM, ← hR, ← hdA, ← hdS]
      refine Prod.ext (funext fun v => (hf1 v).symm)
        (Prod.ext (funext fun r => (hf2 r).symm) (funext fun p => (hf3 p).symm))
    have hf1R : f1 R = some R := by
      rw [hf1 R, if_neg hRi]
      exact numclust_rev_f1_die lab M R R (hMroot R hRmem) hRmem
    have hf2R : f2 R = dth R := by rw [hf2 R, if_neg hRne]
    have hdthR : dth R = ⊤ := hMtop R hRmem
    rw [htriple]
    show numclust_rev_Inv g σ t f1 f2 f3
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- I0 (else)
      intro v
      by_cases hvi : v = i
      · rw [hvi, hf1 i, if_pos rfl]
        exact iff_of_true (by simp) (by rw [hσi])
      · have hcvne : (σ.symm v : ℕ) ≠ t := hsyminj v hvi
        rw [hf1 v, if_neg hvi]
        constructor
        · intro his
          by_cases hnone : lab v = none
          · rw [hnone] at his; simp at his
          · obtain ⟨x, hlx⟩ : ∃ x, lab v = some x := by
              rcases hh : lab v with _ | x
              · exact absurd hh hnone
              · exact ⟨x, rfl⟩
            have := (hI0 v).mp (by rw [hlx]; simp : (lab v).isSome = true)
            omega
        · intro hle
          have h1 : t + 1 ≤ (σ.symm v : ℕ) := by omega
          by_cases hnone : lab v = none
          · have hls : (lab v).isSome = true := (hI0 v).mpr h1
            rw [hnone] at hls
            simp at hls
          · obtain ⟨x, hlx⟩ : ∃ x, lab v = some x := by
              rcases hh : lab v with _ | x
              · exact absurd hh hnone
              · exact ⟨x, rfl⟩
            rw [hlx, Option.bind_some]
            by_cases hxM : x ∈ M <;> simp [hxM]
    · -- I1 (else)
      intro r
      by_cases hrdA : r ∈ dA
      · have hrdA' : r ∈ M.erase R := by rw [← hdA]; exact hrdA
        obtain ⟨hrne, hrM⟩ := Finset.mem_erase.mp hrdA'
        have hrr := hMroot r hrM
        have hf1r : f1 r = some R := by
          rw [hf1 r]
          by_cases hri : r = i
          · rw [hri, if_pos rfl]
          · rw [if_neg hri]; exact numclust_rev_f1_die lab M R r hrr hrM
        have hf2r : f2 r = (g i : EReal) := by rw [hf2 r, if_pos hrdA]
        rw [hf1r, hf2r]
        constructor
        · intro heq; rw [Option.some.injEq] at heq; exact absurd heq.symm hrne
        · intro heq; exact absurd heq (EReal.coe_ne_top (g i))
      · by_cases hrR : r = R
        · rw [hrR, hf1R, hf2R, hdthR]; exact iff_of_true rfl rfl
        · have hf2r : f2 r = dth r := by rw [hf2 r, if_neg hrdA]
          rw [hf2r]
          by_cases hri : r = i
          · rw [hri, hf1 i, if_pos rfl, hdthi]
            exact iff_of_false (fun heq => hRi (by rw [Option.some.injEq] at heq; exact heq))
              (fun heq => absurd heq (by simp))
          · have key : f1 r = some r ↔ lab r = some r := by
              constructor
              · intro heq
                rw [hf1 r, if_neg hri] at heq
                by_cases hnone : lab r = none
                · simp [hnone] at heq ⊢
                · obtain ⟨x, hlx⟩ : ∃ x, lab r = some x := by
                    rcases hh : lab r with _ | x
                    · exact absurd hh hnone
                    · exact ⟨x, rfl⟩
                  rw [hlx, Option.bind_some] at heq
                  by_cases hxM : x ∈ M
                  · rw [if_pos hxM] at heq
                    rw [Option.some.injEq] at heq
                    exact absurd heq.symm hrR
                  · rw [if_neg hxM] at heq
                    rw [Option.some.injEq] at heq
                    rw [heq] at hlx
                    exact hlx
              · intro hl
                rw [hf1 r, if_neg hri]
                have hrM : r ∉ M := by
                  intro hrm
                  exact hrdA (by rw [hdA]; exact Finset.mem_erase.mpr ⟨hrR, hrm⟩)
                rw [hl, Option.bind_some, if_neg hrM]
            rw [key]; exact hI1 r
    · -- I2 (else)
      intro v r h
      by_cases hvi : v = i
      · rw [hvi, hf1 i, if_pos rfl] at h
        rw [Option.some.injEq] at h
        rw [← h]; exact hf1R
      · rw [hf1 v, if_neg hvi] at h
        by_cases hnone : lab v = none
        · rw [hnone] at h; simp at h
        · obtain ⟨x, hlx⟩ : ∃ x, lab v = some x := by
            rcases hh : lab v with _ | x
            · exact absurd hh hnone
            · exact ⟨x, rfl⟩
          rw [hlx, Option.bind_some] at h
          by_cases hxM : x ∈ M
          · rw [if_pos hxM] at h
            rw [Option.some.injEq] at h
            rw [← h]; exact hf1R
          · rw [if_neg hxM] at h
            rw [Option.some.injEq] at h
            rw [← h]
            have hxx : lab x = some x := hI2 v x hlx
            have hxi : x ≠ i := by
              intro h2
              rw [h2] at hxx
              exact absurd (by rw [hxx]; simp : (lab i).isSome = true) hnsi
            rw [hf1 x, if_neg hxi]
            exact numclust_rev_f1_fix lab M R x hxx hxM
    · -- I4 (else)
      intro r hd
      by_cases hrdA : r ∈ dA
      · have hrdA' : r ∈ M.erase R := by rw [← hdA]; exact hrdA
        obtain ⟨hrne, hrM⟩ := Finset.mem_erase.mp hrdA'
        have hrr := hMroot r hrM
        have hf1r : f1 r = some R := by
          rw [hf1 r]
          by_cases hri : r = i
          · rw [hri, if_pos rfl]
          · rw [if_neg hri]; exact numclust_rev_f1_die lab M R r hrr hrM
        rw [hf1r]; simp
      · rw [hf2 r, if_neg hrdA] at hd
        have hls : (lab r).isSome = true := hI4 r hd
        by_cases hri : r = i
        · rw [hri, hf1 i, if_pos rfl]; simp
        · rw [hf1 r, if_neg hri]
          exact numclust_rev_bind_isSome (lab r) _
            (fun a => by by_cases ha : a ∈ M <;> simp [ha]) hls
    · -- I5 (else): the new accumulator is the old count plus one unit per new strict death.
      intro p
      have hdAmem : ∀ r : Fin n, r ∈ dA → r ∈ M := by
        intro r hr; rw [hdA] at hr; exact (Finset.mem_erase.mp hr).2
      have hdAtop : ∀ r : Fin n, r ∈ dA → dth r = ⊤ := fun r hr => hMtop r (hdAmem r hr)
      -- Key set identity: new real-death filter = old real-death filter ∪ new strict deaths.
      have hbox : numclust_rev_deathFilter g f2 p =
          numclust_rev_deathFilter g dth p ∪
            dS.filter (fun r => p = ((g r : EReal), (g i : EReal))) := by
        refine Finset.ext fun r => ?_
        simp only [numclust_rev_deathFilter, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_union]
        by_cases hrA : r ∈ dA
        · constructor
          · rintro ⟨d, hd1, hd2, hd3⟩
            refine Or.inr ⟨?_, ?_⟩
            · have hf2r : f2 r = (g i : EReal) := by rw [hf2 r, if_pos hrA]
              rw [hf2r] at hd1
              rw [EReal.coe_eq_coe_iff] at hd1
              rw [← hd1] at hd3
              rw [hdS]
              exact Finset.mem_filter.mpr ⟨hrA, hd3⟩
            · rw [← hd1] at hd2
              rw [hf2 r, if_pos hrA] at hd2
              exact hd2
          · rintro (⟨d, hd1, _, _⟩ | ⟨hrS, hrQ⟩)
            · exact absurd (hd1.symm.trans (hdAtop r hrA)) (EReal.coe_ne_top d)
            · rw [hdS] at hrS
              exact ⟨(g i : ℝ), by rw [hf2 r, if_pos hrA], hrQ,
                (Finset.mem_filter.mp hrS).2⟩
        · constructor
          · rintro ⟨d, hd1, hd2, hd3⟩
            refine Or.inl ⟨d, ?_, hd2, hd3⟩
            exact (by rw [hf2 r, if_neg hrA] : f2 r = dth r).symm.trans hd1
          · rintro (⟨d, hd1, hd2, hd3⟩ | ⟨hrS, _⟩)
            · exact ⟨d, (by rw [hf2 r, if_neg hrA]; exact hd1), hd2, hd3⟩
            · rw [hdS] at hrS
              exact absurd (Finset.mem_filter.mp hrS).1 hrA
      have hdisj : Disjoint (numclust_rev_deathFilter g dth p)
          (dS.filter (fun r => p = ((g r : EReal), (g i : EReal)))) := by
        rw [Finset.disjoint_iff_ne]
        rintro r hrD b bmem con
        simp only [numclust_rev_deathFilter, Finset.mem_filter, Finset.mem_univ, true_and] at hrD
        obtain ⟨d, hd1, _, _⟩ := hrD
        have hrA : b ∈ dA := by
          rw [hdS] at bmem
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp bmem).1).1
        have htop := hdAtop b hrA
        rw [← con] at htop
        exact absurd (hd1.symm.trans htop) (EReal.coe_ne_top d)
      rw [hf3 p, hI5 p, Finset.sum_boole, hbox, Finset.card_union_of_disjoint hdisj]
      rfl

private theorem numclust_rev_jointRun_inv (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    numclust_rev_Inv g σ 0 (numclust_rev_jointRun n g Dm δ σ).1
      (numclust_rev_jointRun n g Dm δ σ).2.1
      (numclust_rev_jointRun n g Dm δ σ).2.2 := by
  have key : ∀ j : ℕ, j ≤ n → numclust_rev_Inv g σ (n - j)
      ((((List.finRange n).reverse).take j).foldl
          (fun st k => numclust_rev_jointStep g Dm δ σ st (σ k))
          ((fun _ => none), (fun _ => ⊥), (fun _ => 0))).1
      ((((List.finRange n).reverse).take j).foldl
          (fun st k => numclust_rev_jointStep g Dm δ σ st (σ k))
          ((fun _ => none), (fun _ => ⊥), (fun _ => 0))).2.1
      ((((List.finRange n).reverse).take j).foldl
          (fun st k => numclust_rev_jointStep g Dm δ σ st (σ k))
          ((fun _ => none), (fun _ => ⊥), (fun _ => 0))).2.2 := by
    intro j hj
    induction j with
    | zero =>
      simp only [List.take_zero, List.foldl_nil]
      exact numclust_rev_Inv_init g σ
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
      refine numclust_rev_Inv_step g Dm δ σ hσ (n - (j+1)) (by omega) _ _ _ ?_
      simpa only [show n - (j + 1) + 1 = n - j by omega] using ih (by omega)
  have hfinal : List.take n (List.finRange n).reverse = (List.finRange n).reverse := by
    apply List.take_of_length_le
    rw [List.length_reverse, List.length_finRange]
  simpa only [numclust_rev_jointRun, hfinal, Nat.sub_self] using key n (Nat.le_refl n)

/-! ### (BD) barcode multiplicities from the private death map -/

private theorem numclust_rev_BD_repr (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) (p : EReal × EReal) :
    ripsBarcode g Dm δ σ p
      = ((numclust_rev_jointRun n g Dm δ σ).2.2 p +
          (Finset.univ.filter (fun r => numclust_rev_barDeath n g Dm δ σ r = ⊤)).sum
            (fun r => if p = ((g r : EReal), ⊥) then (1 : ℕ∞) else 0)) := by
  have hInv := numclust_rev_jointRun_inv n g Dm δ σ hσ
  obtain ⟨_, hI1, _, _, _⟩ := hInv
  have hips : Finset.univ.filter (fun r : Fin n => (barRun g Dm δ σ).1 r = some r)
      = Finset.univ.filter (fun r => numclust_rev_barDeath n g Dm δ σ r = ⊤) := by
    apply Finset.filter_congr
    intro r _
    have hb : (barRun g Dm δ σ).1 r = numclust_rev_finalLab n g Dm δ σ r := by
      rw [← numclust_rev_jointRun_proj]
    rw [hb, numclust_rev_finalLab]
    exact hI1 r
  simp only [ripsBarcode, hips]
  rw [← numclust_rev_jointRun_proj]

private theorem numclust_rev_BD_real (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    ∀ b d : EReal, d ≠ ⊥ → d ≠ ⊤ →
      ripsBarcode g Dm δ σ (b, d)
        = ((Finset.univ.filter (fun r =>
              numclust_rev_barDeath n g Dm δ σ r = d ∧ (g r : EReal) = b ∧
                (d : EReal) < (g r : EReal))).card : ℕ∞) := by
  intro b d h1 h2
  have hInv := numclust_rev_jointRun_inv n g Dm δ σ hσ
  obtain ⟨_, _, _, _, hI5⟩ := hInv
  have hsum0 : (Finset.univ.filter (fun r => numclust_rev_barDeath n g Dm δ σ r = ⊤)).sum
      (fun r => if (b, d) = ((g r : EReal), (⊥ : EReal)) then (1 : ℕ∞) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    by_cases hq : (b, d) = ((g r : EReal), ⊥)
    · rw [if_pos hq]
      exact absurd (Prod.ext_iff.mp hq).2 h1
    · rw [if_neg hq]
  have hdeq : numclust_rev_deathFilter g ((numclust_rev_jointRun n g Dm δ σ).2.1) (b, d)
      = Finset.univ.filter (fun r => numclust_rev_barDeath n g Dm δ σ r = d ∧
          (g r : EReal) = b ∧ (d : EReal) < (g r : EReal)) := by
    apply Finset.filter_congr
    intro r _
    constructor
    · rintro ⟨e, he1, he2, he3⟩
      obtain ⟨hb', hd'⟩ := Prod.ext_iff.mp he2
      change b = (g r : EReal) at hb'
      change d = ((e : ℝ) : EReal) at hd'
      exact ⟨he1.trans hd'.symm, hb'.symm, by rw [hd']; exact he3⟩
    · rintro ⟨h1', h2', h3'⟩
      simp only [numclust_rev_barDeath] at h1'
      obtain ⟨e0, he0⟩ : ∃ e : ℝ, d = ((e : EReal)) := by
        have hmem : d ∈ Set.range (fun x : ℝ => ((x : EReal))) := by
          rw [EReal.range_coe]
          simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨h1, h2⟩
        obtain ⟨e, he⟩ := hmem
        exact ⟨e, he.symm⟩
      exact ⟨e0, by rw [h1', he0], by rw [← h2', ← he0], by rw [← he0]; exact h3'⟩
  rw [numclust_rev_BD_repr n g Dm δ σ hσ (b, d), hsum0, add_zero, hI5 (b, d), hdeq]

private theorem numclust_rev_BD_immortal (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    ∀ b : EReal,
      ripsBarcode g Dm δ σ (b, ⊥)
        = ((Finset.univ.filter (fun r =>
              numclust_rev_barDeath n g Dm δ σ r = ⊤ ∧ (g r : EReal) = b)).card : ℕ∞) := by
  intro b
  have hInv := numclust_rev_jointRun_inv n g Dm δ σ hσ
  obtain ⟨_, _, _, _, hI5⟩ := hInv
  have hacc0 : numclust_rev_deathFilter g ((numclust_rev_jointRun n g Dm δ σ).2.1) (b, ⊥) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro r _
    rintro ⟨e, _, he2, _⟩
    exact absurd (congrArg Prod.snd he2) (EReal.bot_ne_coe e)
  have hsum : (Finset.univ.filter (fun r => numclust_rev_barDeath n g Dm δ σ r = ⊤)).sum
      (fun r => if (b, ⊥) = ((g r : EReal), (⊥ : EReal)) then (1 : ℕ∞) else 0)
      = ((Finset.univ.filter (fun r => numclust_rev_barDeath n g Dm δ σ r = ⊤ ∧
          (g r : EReal) = b)).card : ℕ∞) := by
    rw [Finset.sum_boole]
    have hff : (Finset.univ.filter (fun r => numclust_rev_barDeath n g Dm δ σ r = ⊤)).filter
        (fun r => (b, ⊥) = ((g r : EReal), (⊥ : EReal)))
        = Finset.univ.filter (fun r => numclust_rev_barDeath n g Dm δ σ r = ⊤ ∧
            (g r : EReal) = b) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro r _
      constructor
      · rintro ⟨hB, hP⟩
        exact ⟨hB, (congrArg Prod.fst hP).symm⟩
      · rintro ⟨hB, hb⟩
        exact ⟨hB, by rw [hb]⟩
    rw [hff]
  rw [numclust_rev_BD_repr n g Dm δ σ hσ (b, ⊥), hsum, hI5 (b, ⊥), hacc0,
    Finset.card_empty, Nat.cast_zero, zero_add]

private theorem numclust_rev_BD_top (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    ∀ b : EReal, ripsBarcode g Dm δ σ (b, ⊤) = 0 := by
  intro b
  have hInv := numclust_rev_jointRun_inv n g Dm δ σ hσ
  obtain ⟨_, _, _, _, hI5⟩ := hInv
  have hacc0 : numclust_rev_deathFilter g ((numclust_rev_jointRun n g Dm δ σ).2.1) (b, ⊤) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro r _
    rintro ⟨e, _, he2, _⟩
    exact absurd (congrArg Prod.snd he2).symm (EReal.coe_ne_top e)
  have hsum0 : (Finset.univ.filter (fun r => numclust_rev_barDeath n g Dm δ σ r = ⊤)).sum
      (fun r => if (b, ⊤) = ((g r : EReal), (⊥ : EReal)) then (1 : ℕ∞) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    by_cases hq : (b, ⊤) = ((g r : EReal), (⊥ : EReal))
    · rw [if_pos hq]
      exact absurd (congrArg Prod.snd hq).symm (by simp)
    · rw [if_neg hq]
  rw [numclust_rev_BD_repr n g Dm δ σ hσ (b, ⊤), hsum0, add_zero, hI5 (b, ⊤), hacc0,
    Finset.card_empty, Nat.cast_zero]

/-! ### (R) coupling of the τ-sweep with the plain sweep -/

/-- One coupled step: advance the τ-sweep and the plain (label+death) sweep together. -/
private def numclust_rev_cstep (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ τ : ℝ)
    (σ : Fin n ≃ Fin n) (st : UFState n × UFState n × (Fin n → EReal)) (i : Fin n) :
    UFState n × UFState n × (Fin n → EReal) :=
  (ufStep g Dm δ τ σ st.1 i,
   (numclust_rev_jointStep g Dm δ σ (st.2.1, st.2.2, (fun _ => 0)) i).1,
   (numclust_rev_jointStep g Dm δ σ (st.2.1, st.2.2, (fun _ => 0)) i).2.1)

/-- The full coupled run. -/
private def numclust_rev_cRun (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ τ : ℝ)
    (σ : Fin n ≃ Fin n) : UFState n × UFState n × (Fin n → EReal) :=
  (List.finRange n).reverse.foldl (fun st k => numclust_rev_cstep n g Dm δ τ σ st (σ k))
    ((fun _ => none), (fun _ => none), (fun _ => ⊥))

/-- Coupling invariant at threshold `t`: same processed set, τ-rootedness, refinement of the
plain partition by the τ partition, and the per-root survivor characterization
(Claim K) at the prefix. -/
private def numclust_rev_CI {n : ℕ} (g : Fin n → ℝ) (τ : ℝ) (σ : Fin n ≃ Fin n) (t : ℕ)
    (T lab : UFState n) (dth : Fin n → EReal) : Prop :=
  (∀ v : Fin n, (T v).isSome = true ↔ t ≤ (σ.symm v : ℕ)) ∧
  (∀ v r : Fin n, T v = some r → T r = some r) ∧
  (∀ v r : Fin n, T v = some r → lab v = lab r) ∧
  (∀ r : Fin n, (lab r = some r ∨ ((dth r : EReal) ≠ ⊥ ∧ (dth r : EReal) ≠ ⊤ ∧
      (dth r) + (τ : EReal) ≤ (g r : EReal))) → T r = some r) ∧
  -- CI-5 (att32 repair): prominence weakened to a REAL death. The prominence form is
  -- unprovable at the merge (the DPR configuration: a plain-merged root in Minf.erase
  -- Rinf whose τ-entry is δ-disconnected at the step survives with gap < τ; excluding
  -- it would need a τ-side max-g-root invariant that is absent from the CI, per att27).
  -- Downstream consumes only conjunct 4 (verified: hCI.2.2.2.1), so this is loss-free.
  (∀ r : Fin n, T r = some r → (lab r = some r ∨ ((dth r : EReal) ≠ ⊥ ∧
      (dth r : EReal) ≠ ⊤))) ∧
  -- CI-6 (att32 repair): the old-owns SPLIT form was FALSE (saddle configuration:
  -- r = Rτ ∉ Minf has T' i = some Rτ but lab' i = some Rinf ≠ some r); re-formed as a
  -- duplicate of CI-5 (self-labelled ∨ real death), which the merge preserves.
  (∀ r : Fin n, T r = some r → (lab r = some r ∨ ((dth r : EReal) ≠ ⊥ ∧
      (dth r : EReal) ≠ ⊤))) ∧
  (∀ r : Fin n, (dth r : EReal) ≠ ⊥ ∧ (dth r : EReal) ≠ ⊤ →
      ∀ k : Fin n, (k : ℕ) < t → (g (σ k) : EReal) ≤ dth r) ∧
  -- 8th (CI-ELD): every plain entry's root is the σ-eldest (max-`g`, max-`σ.symm`)
  -- member of its own entry. (Maintained by the elder rule; used for the redirect
  -- comparisons and to rule out the cross-entry death regimes.)
  (∀ v r : Fin n, lab v = some r → (σ.symm v : ℕ) ≤ (σ.symm r : ℕ))

private theorem numclust_rev_cstep_uf {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (st : UFState n × UFState n × (Fin n → EReal))
    (i : Fin n) :
    (numclust_rev_cstep n g Dm δ τ σ st i).1 = ufStep g Dm δ τ σ st.1 i := rfl

private theorem numclust_rev_cstep_lab {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (st : UFState n × UFState n × (Fin n → EReal))
    (i : Fin n) :
    (numclust_rev_cstep n g Dm δ τ σ st i).2.1
      = (numclust_rev_jointStep g Dm δ σ (st.2.1, st.2.2, (fun _ => 0)) i).1 := rfl

private theorem numclust_rev_cstep_dth {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (st : UFState n × UFState n × (Fin n → EReal))
    (i : Fin n) :
    (numclust_rev_cstep n g Dm δ τ σ st i).2.2
      = (numclust_rev_jointStep g Dm δ σ (st.2.1, st.2.2, (fun _ => 0)) i).2.1 := rfl

private theorem numclust_rev_cRun_fst {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (l : List (Fin n))
    (init : UFState n × UFState n × (Fin n → EReal)) :
    (l.foldl (fun st k => numclust_rev_cstep n g Dm δ τ σ st (σ k)) init).1
      = l.foldl (fun st k => ufStep g Dm δ τ σ st (σ k)) init.1 := by
  induction l generalizing init with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.foldl_cons]
    exact ih (numclust_rev_cstep n g Dm δ τ σ init (σ k))

private theorem numclust_rev_cRun_snd {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (l : List (Fin n))
    (init : UFState n × UFState n × (Fin n → EReal)) :
    ((l.foldl (fun st k => numclust_rev_cstep n g Dm δ τ σ st (σ k)) init).2.1,
     (l.foldl (fun st k => numclust_rev_cstep n g Dm δ τ σ st (σ k)) init).2.2)
      = ((l.foldl (fun (st : UFState n × (Fin n → EReal)) k =>
              ((numclust_rev_jointStep g Dm δ σ (st.1, st.2, (fun _ => 0)) (σ k)).1,
               (numclust_rev_jointStep g Dm δ σ (st.1, st.2, (fun _ => 0)) (σ k)).2.1))
            (init.2.1, init.2.2)).1,
         (l.foldl (fun (st : UFState n × (Fin n → EReal)) k =>
              ((numclust_rev_jointStep g Dm δ σ (st.1, st.2, (fun _ => 0)) (σ k)).1,
               (numclust_rev_jointStep g Dm δ σ (st.1, st.2, (fun _ => 0)) (σ k)).2.1))
            (init.2.1, init.2.2)).2) := by
  obtain ⟨T, lab, dth⟩ := init
  induction l generalizing T lab dth with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.foldl_cons, numclust_rev_cstep]
    exact ih (ufStep g Dm δ τ σ T (σ k))
      (numclust_rev_jointStep g Dm δ σ (lab, dth, (fun _ => 0)) (σ k)).1
      (numclust_rev_jointStep g Dm δ σ (lab, dth, (fun _ => 0)) (σ k)).2.1

/-- The pair-fold (acc reset each step) has the same label/death projections as the triple
fold (arbitrary initial accumulator). -/
private theorem numclust_rev_pairTriple_bridge {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (l : List (Fin n)) (lab : UFState n) (dth : Fin n → EReal)
    (acc : (EReal × EReal) → ℕ∞) :
    ((l.foldl (fun (st : UFState n × (Fin n → EReal)) k =>
          ((numclust_rev_jointStep g Dm δ σ (st.1, st.2, (fun _ => 0)) (σ k)).1,
           (numclust_rev_jointStep g Dm δ σ (st.1, st.2, (fun _ => 0)) (σ k)).2.1))
        (lab, dth)).1,
     (l.foldl (fun (st : UFState n × (Fin n → EReal)) k =>
          ((numclust_rev_jointStep g Dm δ σ (st.1, st.2, (fun _ => 0)) (σ k)).1,
           (numclust_rev_jointStep g Dm δ σ (st.1, st.2, (fun _ => 0)) (σ k)).2.1))
        (lab, dth)).2)
      = ((l.foldl (fun st k => numclust_rev_jointStep g Dm δ σ st (σ k)) (lab, dth, acc)).1,
         (l.foldl (fun st k => numclust_rev_jointStep g Dm δ σ st (σ k)) (lab, dth, acc)).2.1) := by
  induction l generalizing lab dth acc with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.foldl_cons]
    have hacc : ((numclust_rev_jointStep g Dm δ σ (lab, dth, (fun _ => 0)) (σ k)).1,
        (numclust_rev_jointStep g Dm δ σ (lab, dth, (fun _ => 0)) (σ k)).2.1)
      = ((numclust_rev_jointStep g Dm δ σ (lab, dth, acc) (σ k)).1,
        (numclust_rev_jointStep g Dm δ σ (lab, dth, acc) (σ k)).2.1) := by
      by_cases hS : numclust_rev_neighSet Dm δ lab (σ k) = ∅
      · simp only [numclust_rev_jointStep, dif_pos hS]
      · rw [numclust_rev_jointStep_ne g Dm δ σ lab dth (fun _ => 0) (σ k) hS,
            numclust_rev_jointStep_ne g Dm δ σ lab dth acc (σ k) hS]
    have key := ih ((numclust_rev_jointStep g Dm δ σ (lab, dth, acc) (σ k)).1)
      ((numclust_rev_jointStep g Dm δ σ (lab, dth, acc) (σ k)).2.1)
      ((numclust_rev_jointStep g Dm δ σ (lab, dth, acc) (σ k)).2.2)
    rw [Prod.ext_iff] at key
    obtain ⟨h1, h2⟩ := key
    rw [hacc]
    exact Prod.ext_iff.mpr ⟨h1, h2⟩

private theorem numclust_rev_cRun_proj {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) :
    (numclust_rev_cRun n g Dm δ τ σ).1 = ufRun g Dm δ τ σ ∧
    ((numclust_rev_cRun n g Dm δ τ σ).2.1, (numclust_rev_cRun n g Dm δ τ σ).2.2)
      = ((numclust_rev_jointRun n g Dm δ σ).1, (numclust_rev_jointRun n g Dm δ σ).2.1) := by
  constructor
  · simp only [numclust_rev_cRun, ufRun]
    exact numclust_rev_cRun_fst g Dm δ τ σ (List.finRange n).reverse
      ((fun _ => none), (fun _ => none), (fun _ => ⊥))
  · simp only [numclust_rev_cRun]
    rw [numclust_rev_cRun_snd (n := n) g Dm δ τ σ (List.finRange n).reverse
      ((fun _ => none), (fun _ => none), (fun _ => ⊥))]
    simp only [numclust_rev_jointRun]
    exact numclust_rev_pairTriple_bridge g Dm δ σ (List.finRange n).reverse
      (fun _ => none) (fun _ => ⊥) (fun _ => 0)

/-- The accumulator-free core of the plain-sweep invariant. -/
private def numclust_rev_InvCore {n : ℕ} (g : Fin n → ℝ) (σ : Fin n ≃ Fin n) (t : ℕ)
    (lab : UFState n) (dth : Fin n → EReal) : Prop :=
  (∀ v : Fin n, (lab v).isSome = true ↔ t ≤ (σ.symm v : ℕ)) ∧
  (∀ r : Fin n, lab r = some r ↔ dth r = ⊤) ∧
  (∀ v r : Fin n, lab v = some r → lab r = some r) ∧
  (∀ r : Fin n, dth r ≠ ⊥ → (lab r).isSome = true)

private theorem numclust_rev_InvCore_of_Inv {n : ℕ} (g : Fin n → ℝ) (σ : Fin n ≃ Fin n)
    (t : ℕ) (lab : UFState n) (dth : Fin n → EReal) (acc : (EReal × EReal) → ℕ∞)
    (h : numclust_rev_Inv g σ t lab dth acc) : numclust_rev_InvCore g σ t lab dth :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Coupling step of the τ-sweep with the plain sweep. -/
private theorem numclust_rev_CI_step {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ)
    (t : ℕ) (ht : t < n) (i : Fin n) (hiσ : σ.symm i = ⟨t, ht⟩)
    (T lab : UFState n) (dth : Fin n → EReal)
    (hCI : numclust_rev_CI g τ σ (t+1) T lab dth)
    (hInv : numclust_rev_InvCore g σ (t+1) lab dth) :
    numclust_rev_CI g τ σ t
      (numclust_rev_cstep n g Dm δ τ σ (T, lab, dth) i).1
      (numclust_rev_cstep n g Dm δ τ σ (T, lab, dth) i).2.1
      (numclust_rev_cstep n g Dm δ τ σ (T, lab, dth) i).2.2 := by
  obtain ⟨hA1, hA2, hREF, hKback, hKfwd, hSPLIT, hA4, hEl⟩ := hCI
  obtain ⟨hI0, hI1, hI2, hI3⟩ := hInv
  have hSymmI : (σ.symm i : ℕ) = t := by rw [hiσ]
  have hSymmEq : ∀ v : Fin n, (σ.symm v : ℕ) = t → v = i := by
    intro v h
    exact σ.symm.injective (Fin.val_injective (by rw [hSymmI]; exact h))
  have hmono : ∀ x y : Fin n, (σ.symm x : ℕ) ≤ (σ.symm y : ℕ) → g x ≤ g y := by
    intro x y h
    have hxy : σ.symm x ≤ σ.symm y := Fin.le_def.mpr h
    simpa using hσ hxy
  have hTi : T i = none := by
    cases h : T i with
    | none => rfl
    | some x => exact absurd ((hA1 i).mp (by rw [h]; simp)) (by rw [hSymmI]; omega)
  have hlabi : lab i = none := by
    cases h : lab i with
    | none => rfl
    | some x => exact absurd ((hI0 i).mp (by rw [h]; simp)) (by rw [hSymmI]; omega)
  have hSeq : numclust_rev_neighSet Dm δ T i = numclust_rev_neighSet Dm δ lab i := by
    apply Finset.filter_congr
    intro j _
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (hI0 j).mpr ((hA1 j).mp h3)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, (hA1 j).mpr ((hI0 j).mp h3)⟩
  simp only [numclust_rev_cstep, Prod.fst, Prod.snd]
  by_cases hS : numclust_rev_neighSet Dm δ lab i = ∅
  · -- PEAK: `i` starts a fresh entry in both sweeps; no merge, no death.
    have hST : numclust_rev_neighSet Dm δ T i = ∅ := by rw [hSeq]; exact hS
    simp only [numclust_rev_jointStep, dif_pos hS, ufStep, if_pos hST]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        rcases h with h | ⟨h1, h2, h3⟩
        · exact hKback r (Or.inl h)
        · exact hKback r (Or.inr ⟨h1, h2, h3⟩)
    · -- Kfwd (repaired CI-5): τ-root ⇒ plain-root ∨ real death
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
    · -- Kfwd dup (repaired CI-6): τ-root ⇒ plain-root ∨ real death
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
    · -- A4: recorded deaths dominate all future levels
      intro r hr k hk
      by_cases hri : r = i
      · rw [hri, Function.update_self] at hr
        exact absurd rfl hr.2
      · simp only [Function.update_of_ne hri] at hr
        simp only [Function.update_of_ne hri]
        exact hA4 r hr k (by omega)
    · -- CI-ELD: the elder rule is preserved; `i` is a fresh self-labeled peak.
      intro v r h
      by_cases hvi : v = i
      · rw [hvi, Function.update_self] at h
        simp only [Option.some.injEq] at h
        rw [hvi, ← h]
      · simp only [Function.update_of_ne hvi] at h
        exact hEl v r h
  · -- MERGE: the E-phase case analysis; see the roadmap in
    -- /tmp/opencode/agents/numclust_rev_explanation.md (agent-B).
    -- Goal: `numclust_rev_CI g τ σ t T' lab' dth'` for the post-merge state,
    -- where T' = ufStep g Dm δ τ σ T i, lab' = (jointStep … i).1,
    -- dth' = (jointStep … i).2.1. Split into the 7 CI components (easiest first).
    -- Expose the plain else-branch only; keep ufStep folded and bridge it to our own
    -- syntax via hT'uf below (same ite-at-function-type shape ⇒ rfl/defeq works).
    have hST : numclust_rev_neighSet Dm δ T i ≠ ∅ := by rw [hSeq]; exact hS
    simp only [numclust_rev_jointStep, dif_neg hS]
    -- Name the plain-side pieces that also appear in lab'/dth' (jointStep's else-branch):
    -- (kept for C4/C5/C6; the τ-side never unfolds ufStep in the goal itself)
    -- τ-side pieces in our own syntax (S_τ = S_∞ by hSeq):
    set Sτ := Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (T j).isSome = true) with hSτ
    set riτ := (T (firstProcessed σ Sτ i)).getD (firstProcessed σ Sτ i) with hriτ
    set Mτ := insert riτ ((Sτ.image (fun j => (T j).getD j)).filter (fun r => g r - g i < τ)) with hMτ
    set Rτ := firstProcessed σ Mτ riτ with hRτ
    set hl2 : Fin n → Option (Fin n) := fun u =>
      if u = i then some Rτ
      else match T u with
        | some x => if x ∈ Mτ then some Rτ else some x
        | none => none with hhl2
    set Eτ := firstProcessed σ (Sτ.image (fun j =>
        (if j = i then some Rτ
          else match T j with
            | some x => if x ∈ Mτ then some Rτ else some x
            | none => none).getD j)) Rτ with hEτ
    -- T'my with the per-vertex lab2 body INLINED (no wrappable local), E-cond naming Eτ:
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
    -- Bridge: (raw ufStep) = T'my (defeq, no pattern matching needed).
    have hT'uf : ∀ w, ufStep g Dm δ τ σ T i w = T'my w := by
      intro w
      simp only [ufStep, if_neg hST]
      simp only [← hSτ, ← hriτ, ← hMτ, ← hRτ]
      rfl
    -- Shared post-merge forward direction (repaired CI conjuncts 5 & 6, att32): every
    -- surviving τ-root is either still self-labelled in lab' or carries a REAL death.
    -- A plain-merged root (Minf.erase Rinf, DPR configuration included) dies at level
    -- g i, which is real; an unmerged plain root keeps its self-label; a real-death
    -- root cannot lie in Minf (Minf roots have dth = ⊤), so its death is unchanged.
    have hKfwdP : ∀ r : Fin n, ufStep g Dm δ τ σ T i r = some r →
        ((fun w => if w = i then some (numclust_rev_eldestRoot σ Dm δ lab i)
            else Option.bind (lab w) (fun a => if a ∈ numclust_rev_mergeSet σ Dm δ lab i
              then some (numclust_rev_eldestRoot σ Dm δ lab i) else some a)) r = some r ∨
          ((fun s => if s ∈ (numclust_rev_mergeSet σ Dm δ lab i).erase
                (numclust_rev_eldestRoot σ Dm δ lab i) then (g i : EReal) else dth s) r ≠ ⊥ ∧
           (fun s => if s ∈ (numclust_rev_mergeSet σ Dm δ lab i).erase
                (numclust_rev_eldestRoot σ Dm δ lab i) then (g i : EReal) else dth s) r ≠ ⊤)) := by
      intro r h
      -- τ-side spine (mirrors C2/C3/C6)
      have hSτne : Sτ.Nonempty := by rw [hSτ]; exact Finset.nonempty_iff_ne_empty.mpr hST
      have hSτmem : ∀ j ∈ Sτ, j ≠ i ∧ (T j).isSome = true := by
        intro j hj; rw [hSτ] at hj
        exact ⟨(Finset.mem_filter.mp hj).2.1, (Finset.mem_filter.mp hj).2.2.2⟩
      have hMτroot : ∀ m ∈ Mτ, T m = some m ∧ m ≠ i := by
        intro m hm
        rw [hMτ] at hm
        rcases Finset.mem_insert.mp hm with rfl | hm'
        · obtain ⟨_, hsome⟩ := hSτmem _ (by rw [hSτ]; exact numclust_rev_firstProcessed_mem σ _ i hSτne)
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
      have hMτne : Mτ.Nonempty := by rw [hMτ]; exact Finset.insert_nonempty _ _
      have hRτmem : Rτ ∈ Mτ := by rw [hRτ]; exact numclust_rev_firstProcessed_mem σ _ _ hMτne
      have hRτroot : T Rτ = some Rτ := (hMτroot Rτ hRτmem).1
      have hRτnei : Rτ ≠ i := (hMτroot Rτ hRτmem).2
      have hEτroot : Eτ ≠ Rτ → T Eτ = some Eτ ∧ Eτ ≠ i := by
        intro hne
        have hmne : (Sτ.image (fun j => (hl2 j).getD j)).Nonempty := hSτne.image _
        have hEmem : Eτ ∈ Sτ.image (fun j => (hl2 j).getD j) := by
          rw [hEτ]; exact numclust_rev_firstProcessed_mem σ _ Rτ hmne
        obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp hEmem
        obtain ⟨hjnei, hsome⟩ := hSτmem j hjS
        cases hTj : T j with
        | none => rw [hTj] at hsome; simp at hsome
        | some s =>
          have hlj : (hl2 j).getD j = (if s ∈ Mτ then some Rτ else some s).getD j := by
            simp only [hhl2, if_neg hjnei, hTj]
          by_cases hsM : s ∈ Mτ
          · have hEE : Eτ = Rτ := by rw [← hjm]; beta_reduce; rw [hlj]; simp [hsM]
            exact absurd hEE hne
          · have hEs : Eτ = s := by rw [← hjm]; beta_reduce; rw [hlj]; simp [hsM]
            refine ⟨?_, ?_⟩
            · rw [hEs]; exact hA2 j s hTj
            · intro hei; rw [hEs] at hei; rw [hei] at hTj
              exact absurd (hA2 _ _ hTj) (by rw [hTi]; simp)
      -- T' r = some r forces the OLD T r = some r (ufStep ite analysis, mirrors C6').
      simp only [hT'uf, hT'my] at h
      have hTr : T r = some r := by
        by_cases hri : r = i
        · exfalso
          rw [hri] at h
          by_cases hE : Eτ ≠ Rτ ∧ g Rτ - g i < τ
          · rw [if_pos hE] at h
            beta_reduce at h
            have hBi : (if i = i then some Rτ else (match T i with
                | some x => if x ∈ Mτ then some Rτ else some x | none => none)) = some Rτ := by
              simp
            rw [hBi] at h
            simp at h
            exact absurd h (hEτroot hE.1).2
          · rw [if_neg hE] at h
            beta_reduce at h
            have hBi : (if i = i then some Rτ else (match T i with
                | some x => if x ∈ Mτ then some Rτ else some x | none => none)) = some Rτ := by
              simp
            rw [hBi] at h
            simp only [Option.some.injEq] at h
            exact hRτnei h
        · by_cases hE : Eτ ≠ Rτ ∧ g Rτ - g i < τ
          · rw [if_pos hE] at h
            beta_reduce at h
            rw [if_neg hri] at h
            cases hT : T r with
            | none => rw [hT] at h; simp at h
            | some x =>
              rw [hT] at h
              by_cases hxM : x ∈ Mτ
              · simp [hxM] at h
                have hTE : T Eτ = some x := by rw [h]; exact hT
                have hEr := (hEτroot hE.1).1
                rw [hTE] at hEr
                rw [Option.some_inj.mp hEr, h]
              · by_cases hxR : x = Rτ
                · exact absurd (hxR ▸ hRτmem) hxM
                · simp only [if_neg hxM] at h
                  rw [if_neg (Option.some_inj.not.mpr hxR)] at h
                  exact h
          · rw [if_neg hE] at h
            beta_reduce at h
            rw [if_neg hri] at h
            cases hT : T r with
            | none => rw [hT] at h; simp at h
            | some x =>
              rw [hT] at h
              by_cases hxM : x ∈ Mτ
              · simp [hxM] at h
                rw [← h] at hT
                have hxR : some x = some Rτ := by rw [← hT]; exact hRτroot
                rw [h] at hxR
                exact hxR
              · simp only [if_neg hxM, Option.some.injEq] at h
                rw [h]
      -- lab-side pieces
      set Minf := numclust_rev_mergeSet σ Dm δ lab i with hMinfdef
      set Rinf := numclust_rev_eldestRoot σ Dm δ lab i with hRinfdef
      have hMroot : ∀ s : Fin n, s ∈ Minf → lab s = some s :=
        numclust_rev_mergeSet_root σ Dm δ lab i hS hI2
      -- forward characterization
      rcases hKfwd r hTr with hlabr | ⟨hd1, hd2⟩
      · -- old plain root: r dies a real death iff plain-merged; else lab' keeps it.
        have hri : r ≠ i := by
          intro h
          rw [h] at hlabr
          exact absurd hlabr (by rw [hlabi]; simp)
        by_cases hrE : r ∈ Minf.erase Rinf
        · -- plain-merged (DPR configuration included): a REAL death at level g i.
          right
          beta_reduce
          rw [if_pos hrE]
          exact ⟨EReal.coe_ne_bot (g i), EReal.coe_ne_top (g i)⟩
        · left
          beta_reduce
          rw [if_neg hri, hlabr, Option.bind_some]
          beta_reduce
          by_cases hrM : r ∈ Minf
          · rw [if_pos hrM]
            have hrRinf : r = Rinf := by
              by_contra hc
              exact hrE (Finset.mem_erase.mpr ⟨hc, hrM⟩)
            rw [hrRinf]
          · rw [if_neg hrM]
      · -- old real death: r ∉ Minf (its roots have dth = ⊤), so dth' r = dth r is real.
        by_cases hrM : r ∈ Minf
        · exfalso
          exact hd2 ((hI1 r).mp (hMroot r hrM))
        · have hrE : ¬ (r ∈ Minf.erase Rinf) := fun hmem => hrM (Finset.mem_erase.mp hmem).2
          right
          beta_reduce
          rw [if_neg hrE]
          exact ⟨hd1, hd2⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- C1 processed-set: ∀ v, (T' v).isSome = true ↔ t ≤ (σ.symm v : ℕ)
      intro v
      simp only [hT'uf, hT'my]
      by_cases hvi : v = i
      · rw [hvi]
        constructor
        · intro _; rw [hSymmI]
        · intro _
          split_ifs <;> beta_reduce <;> simp
      · have hvne : (σ.symm v : ℕ) ≠ t := fun h => hvi (hSymmEq v h)
        constructor
        · intro his
          have hTv : (T v).isSome = true := by
            cases hT : T v with
            | none =>
              exfalso
              split_ifs at his
              all_goals (beta_reduce at his; simp [hT, hvi] at his)
            | some x => simp [hT]
          have := (hA1 v).mp hTv
          omega
        · intro hle
          have hTv : (T v).isSome = true := (hA1 v).mpr (by omega)
          split_ifs
          · beta_reduce
            cases hT : T v with
            | none => rw [hT] at hTv; simp at hTv
            | some x =>
              by_cases hxM : x ∈ Mτ
              · simp [hxM, hT, hvi]
              · simp only [if_neg hxM]; split_ifs <;> simp
          · beta_reduce
            cases hT : T v with
            | none => rw [hT] at hTv; simp at hTv
            | some x => by_cases hxM : x ∈ Mτ <;> simp [hxM, hT, hvi]
    · -- C2 rooted: ∀ v r, T' v = some r → T' r = some r
      intro v r h
      simp only [hT'uf, hT'my] at h
      have hSτne : Sτ.Nonempty := by rw [hSτ]; exact Finset.nonempty_iff_ne_empty.mpr hST
      have hSτmem : ∀ j ∈ Sτ, j ≠ i ∧ (T j).isSome = true := by
        intro j hj; rw [hSτ] at hj; exact ⟨(Finset.mem_filter.mp hj).2.1, (Finset.mem_filter.mp hj).2.2.2⟩
      have hMτroot : ∀ m ∈ Mτ, T m = some m ∧ m ≠ i := by
        intro m hm
        rw [hMτ] at hm
        rcases Finset.mem_insert.mp hm with rfl | hm'
        · obtain ⟨_, hsome⟩ := hSτmem _ (by rw [hSτ]; exact numclust_rev_firstProcessed_mem σ _ i hSτne)
          cases hTf : T (firstProcessed σ Sτ i) with
          | none => rw [hTf] at hsome; simp at hsome
          | some s =>
            have hri : riτ = s := by rw [hriτ, hTf]; simp
            constructor
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
            constructor
            · exact hA2 _ _ hTj
            · intro hsi; rw [hsi] at hTj
              exact absurd (hA2 _ _ hTj) (by rw [hTi]; simp)
      have hMτne : Mτ.Nonempty := by rw [hMτ]; exact Finset.insert_nonempty _ _
      have hRτmem : Rτ ∈ Mτ := by rw [hRτ]; exact numclust_rev_firstProcessed_mem σ _ _ hMτne
      have hRτroot : T Rτ = some Rτ := (hMτroot Rτ hRτmem).1
      have hRτnei : Rτ ≠ i := (hMτroot Rτ hRτmem).2
      have hEτroot : Eτ ≠ Rτ → T Eτ = some Eτ ∧ Eτ ≠ i := by
        intro hne
        have hmne : (Sτ.image (fun j => (hl2 j).getD j)).Nonempty := hSτne.image _
        have hEmem : Eτ ∈ Sτ.image (fun j => (hl2 j).getD j) := by
          rw [hEτ]; exact numclust_rev_firstProcessed_mem σ _ Rτ hmne
        obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp hEmem
        obtain ⟨hjnei, hsome⟩ := hSτmem j hjS
        cases hTj : T j with
        | none => rw [hTj] at hsome; simp at hsome
        | some s =>
          have hlj : (hl2 j).getD j = (if s ∈ Mτ then some Rτ else some s).getD j := by
            simp only [hhl2, if_neg hjnei, hTj]
          by_cases hsM : s ∈ Mτ
          · have hEE : Eτ = Rτ := by rw [← hjm]; beta_reduce; rw [hlj]; simp [hsM]
            exact absurd hEE hne
          · have hEs : Eτ = s := by rw [← hjm]; beta_reduce; rw [hlj]; simp [hsM]
            refine ⟨?_, ?_⟩
            · rw [hEs]; exact hA2 j s hTj
            · intro hei; rw [hEs] at hei; rw [hei] at hTj
              exact absurd (hA2 _ _ hTj) (by rw [hTi]; simp)
      by_cases hvi : v = i
      · rw [hvi] at h
        split_ifs at h with hE
        · beta_reduce at h
          have hBi : (if i = i then some Rτ else (match T i with
              | some x => if x ∈ Mτ then some Rτ else some x | none => none)) = some Rτ := by simp
          rw [hBi] at h
          simp at h
          rw [← h]
          obtain ⟨hTe, hEnei⟩ := hEτroot hE.1
          simp only [hT'uf, hT'my]
          rw [if_pos hE]
          beta_reduce
          by_cases hEM : Eτ ∈ Mτ <;> simp [hEM, hEnei, hTe]
        · beta_reduce at h
          have hBi : (if i = i then some Rτ else (match T i with
              | some x => if x ∈ Mτ then some Rτ else some x | none => none)) = some Rτ := by simp
          rw [hBi] at h
          simp at h
          rw [← h]
          simp only [hT'uf, hT'my]
          rw [if_neg hE]
          beta_reduce
          simp [hRτnei, hRτroot, hRτmem]
      · split_ifs at h with hE
        · beta_reduce at h
          cases hT : T v with
          | none => rw [hT, if_neg hvi] at h; simp at h
          | some x =>
            rw [hT, if_neg hvi] at h
            by_cases hxM : x ∈ Mτ
            · simp [hxM] at h
              rw [← h]
              obtain ⟨hTe, hEnei⟩ := hEτroot hE.1
              simp only [hT'uf, hT'my]
              rw [if_pos hE]
              beta_reduce
              by_cases hEM : Eτ ∈ Mτ <;> simp [hEM, hEnei, hTe]
            · by_cases hxR : x = Rτ
              · exact absurd (hxR ▸ hRτmem) hxM
              · simp only [if_neg hxM, if_neg hxR, Option.some.injEq] at h
                rw [← h]
                have hxroot : T x = some x := hA2 v x hT
                have hxnei : x ≠ i := by { intro hxi; rw [hxi] at hT; exact absurd (hA2 _ _ hT) (by rw [hTi]; simp) }
                simp only [hT'uf, hT'my]
                rw [if_pos hE]
                beta_reduce
                simp only [if_neg hxnei, if_neg hxM, hxroot]
                simp [hxR]
        · beta_reduce at h
          cases hT : T v with
          | none => rw [hT, if_neg hvi] at h; simp at h
          | some x =>
            rw [hT, if_neg hvi] at h
            by_cases hxM : x ∈ Mτ
            · simp [hxM] at h
              rw [← h]
              simp only [hT'uf, hT'my]
              rw [if_neg hE]
              beta_reduce
              simp [hRτnei, hRτroot, hRτmem]
            · simp only [if_neg hxM, Option.some.injEq] at h
              rw [← h]
              have hxroot : T x = some x := hA2 v x hT
              have hxnei : x ≠ i := by { intro hxi; rw [hxi] at hT; exact absurd (hA2 _ _ hT) (by rw [hTi]; simp) }
              simp only [hT'uf, hT'my]
              rw [if_neg hE]
              beta_reduce
              simp only [if_neg hxnei, if_neg hxM, hxroot]
    · -- C3 label-agreement: ∀ v r, T' v = some r → lab' v = lab' r
      intro v r h
      simp only [hT'uf, hT'my] at h
      set Rinf := numclust_rev_eldestRoot σ Dm δ lab i with hRinfdef
      set Minf := numclust_rev_mergeSet σ Dm δ lab i with hMinfdef
      have hKey : ∀ m ∈ Mτ, (fun w => if w = i then some Rinf
          else Option.bind (lab w) (fun a => if a ∈ Minf then some Rinf else some a)) m
          = some Rinf := by
        intro m hm
        have hSτne : Sτ.Nonempty := by rw [hSτ]; exact Finset.nonempty_iff_ne_empty.mpr hST
        have hSτmem : ∀ j ∈ Sτ, j ≠ i ∧ (T j).isSome = true := by
          intro j hj; rw [hSτ] at hj; exact ⟨(Finset.mem_filter.mp hj).2.1, (Finset.mem_filter.mp hj).2.2.2⟩
        have hjSlab : ∀ j ∈ Sτ, j ∈ numclust_rev_neighSet Dm δ lab i := by
          intro j hj
          have h1 : j ∈ numclust_rev_neighSet Dm δ T i := hj
          rwa [hSeq] at h1
        have hwit : ∃ j ∈ Sτ, T j = some m := by
          rw [hMτ] at hm
          rcases Finset.mem_insert.mp hm with rfl | hm'
          · refine ⟨firstProcessed σ Sτ i, numclust_rev_firstProcessed_mem σ _ i hSτne, ?_⟩
            have hsome : (T (firstProcessed σ Sτ i)).isSome = true :=
              (hSτmem _ (numclust_rev_firstProcessed_mem σ _ i hSτne)).2
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
        have hlabj : lab j = some ((lab j).getD j) :=
          numclust_rev_neigh_root Dm δ lab i j (hjSlab j hjS)
        have hrM : (lab j).getD j ∈ Minf := by
          rw [hMinfdef]
          exact (numclust_rev_mem_mergeSet σ Dm δ lab i _).mpr (Or.inr ⟨j, hjSlab j hjS, rfl⟩)
        have hlabm : lab m = some ((lab j).getD j) := by
          rw [← hREF j m hjT]; exact hlabj
        beta_reduce
        by_cases hmi : m = i
        · rw [hmi, if_pos rfl]
        · rw [if_neg hmi, hlabm]
          simp only [Option.bind_some, if_pos hrM]
      -- Spine: from h : T'my v = some r conclude lab' v = lab' r.
      -- Shared helpers (Sτ-member facts, the lab'-computation lemmas, Mτ preimages).
      have hSτne : Sτ.Nonempty := by rw [hSτ]; exact Finset.nonempty_iff_ne_empty.mpr hST
      have hSτmem : ∀ j ∈ Sτ, j ≠ i ∧ (T j).isSome = true := by
        intro j hj; rw [hSτ] at hj; exact ⟨(Finset.mem_filter.mp hj).2.1, (Finset.mem_filter.mp hj).2.2.2⟩
      have hjSlab : ∀ j ∈ Sτ, j ∈ numclust_rev_neighSet Dm δ lab i := by
        intro j hj
        have h1 : j ∈ numclust_rev_neighSet Dm δ T i := hj
        rwa [hSeq] at h1
      have hlabjS : ∀ j ∈ Sτ, lab j = some ((lab j).getD j) :=
        fun j hj => numclust_rev_neigh_root Dm δ lab i j (hjSlab j hj)
      have hrMS : ∀ j ∈ Sτ, (lab j).getD j ∈ Minf := by
        intro j hj
        rw [hMinfdef]
        exact (numclust_rev_mem_mergeSet σ Dm δ lab i _).mpr (Or.inr ⟨j, hjSlab j hj, rfl⟩)
      have hLR : ∀ w s, lab w = some s → s ∈ Minf → (fun w => if w = i then some Rinf
          else Option.bind (lab w) (fun a => if a ∈ Minf then some Rinf else some a)) w
          = some Rinf := by
        intro w s hws hsM
        beta_reduce
        by_cases hwi : w = i
        · rw [hwi, if_pos rfl]
        · rw [if_neg hwi, hws]
          simp only [Option.bind_some, if_pos hsM]
      have hLfix : ∀ w y, w ≠ i → y ≠ i → lab w = lab y → (fun w => if w = i then some Rinf
          else Option.bind (lab w) (fun a => if a ∈ Minf then some Rinf else some a)) w
          = (fun w => if w = i then some Rinf
          else Option.bind (lab w) (fun a => if a ∈ Minf then some Rinf else some a)) y := by
        intro w y hw hy hwl
        beta_reduce
        rw [if_neg hw, if_neg hy, hwl]
      have hI : (fun w => if w = i then some Rinf
          else Option.bind (lab w) (fun a => if a ∈ Minf then some Rinf else some a)) i
          = some Rinf := by
        beta_reduce
        rw [if_pos rfl]
      have hPre : ∀ x ∈ Mτ, ∃ j ∈ Sτ, T j = some x := by
        intro x hx
        rw [hMτ] at hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · refine ⟨firstProcessed σ Sτ i, numclust_rev_firstProcessed_mem σ _ i hSτne, ?_⟩
          have hsome : (T (firstProcessed σ Sτ i)).isSome = true :=
            (hSτmem _ (numclust_rev_firstProcessed_mem σ _ i hSτne)).2
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
      have hRτmem : Rτ ∈ Mτ := by rw [hRτ]; exact numclust_rev_firstProcessed_mem σ _ _ hMτne
      -- Eτ's label: given Eτ ≠ Rτ, Eτ is the τ-root of some Sτ member, hence lab' Eτ = some Rinf.
      have hVEτh : Eτ ≠ Rτ → (fun w => if w = i then some Rinf
          else Option.bind (lab w) (fun a => if a ∈ Minf then some Rinf else some a)) Eτ
          = some Rinf := by
        intro hER
        have hmne : (Sτ.image (fun j => (hl2 j).getD j)).Nonempty := hSτne.image _
        have hEmem : Eτ ∈ Sτ.image (fun j => (hl2 j).getD j) := by
          rw [hEτ]; exact numclust_rev_firstProcessed_mem σ _ Rτ hmne
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
      -- Case analysis, mirroring the banked C2 proof structure on the same h.
      by_cases hvi : v = i
      · rw [hvi] at h
        split_ifs at h with hE
        · beta_reduce at h
          have hBi : (if i = i then some Rτ else (match T i with
              | some x => if x ∈ Mτ then some Rτ else some x | none => none)) = some Rτ := by simp
          rw [hBi] at h
          simp at h
          rw [hvi, ← h]
          rw [hI, hVEτh hE.1]
        · beta_reduce at h
          have hBi : (if i = i then some Rτ else (match T i with
              | some x => if x ∈ Mτ then some Rτ else some x | none => none)) = some Rτ := by simp
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
    · -- C4 entry-back: ∀ r, (lab' r = some r ∨ prominent dth') → T' r = some r
      intro r hr
      set Rinf := numclust_rev_eldestRoot σ Dm δ lab i with hRinfdef
      set Minf := numclust_rev_mergeSet σ Dm δ lab i with hMinfdef
      have hSτne : Sτ.Nonempty := by rw [hSτ]; exact Finset.nonempty_iff_ne_empty.mpr hST
      have hSτmem : ∀ j ∈ Sτ, j ≠ i ∧ (T j).isSome = true := by
        intro j hj; rw [hSτ] at hj; exact ⟨(Finset.mem_filter.mp hj).2.1, (Finset.mem_filter.mp hj).2.2.2⟩
      have hjSlab : ∀ j ∈ Sτ, j ∈ numclust_rev_neighSet Dm δ lab i := by
        intro j hj; have h1 : j ∈ numclust_rev_neighSet Dm δ T i := hj; rwa [hSeq] at h1
      have hlabjS : ∀ j ∈ Sτ, lab j = some ((lab j).getD j) :=
        fun j hj => numclust_rev_neigh_root Dm δ lab i j (hjSlab j hj)
      have hrMS : ∀ j ∈ Sτ, (lab j).getD j ∈ Minf := by
        intro j hj; rw [hMinfdef]
        exact (numclust_rev_mem_mergeSet σ Dm δ lab i _).mpr (Or.inr ⟨j, hjSlab j hj, rfl⟩)
      have hMroot : ∀ r : Fin n, r ∈ Minf → lab r = some r :=
        numclust_rev_mergeSet_root σ Dm δ lab i hS hI2
      have hMne : Minf.Nonempty := by rw [hMinfdef]; exact Finset.insert_nonempty _ _
      have hRinfmem : Rinf ∈ Minf := by
        simpa only [hRinfdef] using numclust_rev_firstProcessed_mem σ _ _ hMne
      have hRinfroot : lab Rinf = some Rinf := hMroot Rinf hRinfmem
      have hiM : i ∉ Minf := by
        rw [hMinfdef]; intro h
        have hSne : (numclust_rev_neighSet Dm δ lab i).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hS
        rcases (numclust_rev_mem_mergeSet σ Dm δ lab i i).mp h with heq | ⟨j, hjS, hrj⟩
        · have hfp := numclust_rev_firstProcessed_mem σ (numclust_rev_neighSet Dm δ lab i) i hSne
          have hlabfp := numclust_rev_neigh_root Dm δ lab i _ hfp
          rw [← heq] at hlabfp
          exact absurd (hI2 _ _ hlabfp) (by rw [hlabi]; simp)
        · have hlabj := numclust_rev_neigh_root Dm δ lab i j hjS
          rw [hrj] at hlabj
          exact absurd (hI2 _ _ hlabj) (by rw [hlabi]; simp)
      have hMτroot : ∀ m ∈ Mτ, T m = some m ∧ m ≠ i := by
        intro m hm
        rw [hMτ] at hm
        rcases Finset.mem_insert.mp hm with rfl | hm'
        · obtain ⟨_, hsome⟩ := hSτmem _ (by rw [hSτ]; exact numclust_rev_firstProcessed_mem σ _ i hSτne)
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
      have hRτmem : Rτ ∈ Mτ := by rw [hRτ]; exact numclust_rev_firstProcessed_mem σ _ _ (by rw [hMτ]; exact Finset.insert_nonempty _ _)
      have hRτroot : T Rτ = some Rτ := (hMτroot Rτ hRτmem).1
      have hRτnei : Rτ ≠ i := (hMτroot Rτ hRτmem).2
      -- lab'-computation helpers (copied from C3)
      have hLR : ∀ w s, lab w = some s → s ∈ Minf → (fun w => if w = i then some Rinf
          else Option.bind (lab w) (fun a => if a ∈ Minf then some Rinf else some a)) w
          = some Rinf := by
        intro w s hws hsM; beta_reduce
        by_cases hwi : w = i
        · rw [hwi, if_pos rfl]
        · rw [if_neg hwi, hws]; simp only [Option.bind_some, if_pos hsM]
      have hLfix : ∀ w y, w ≠ i → y ≠ i → lab w = lab y → (fun w => if w = i then some Rinf
          else Option.bind (lab w) (fun a => if a ∈ Minf then some Rinf else some a)) w
          = (fun w => if w = i then some Rinf
          else Option.bind (lab w) (fun a => if a ∈ Minf then some Rinf else some a)) y := by
        intro w y hw hy hwl; beta_reduce; rw [if_neg hw, if_neg hy, hwl]
      have hI : (fun w => if w = i then some Rinf
          else Option.bind (lab w) (fun a => if a ∈ Minf then some Rinf else some a)) i
          = some Rinf := by beta_reduce; rw [if_pos rfl]
      rcases hr with hlab | hprom
      · -- lab' r = some r case.  Case analysis on the redirect: r = i is absurd
        -- (lab' i = some Rinf, Rinf ∈ Minf, i ∉ Minf); otherwise the old label lab r
        -- decides between unredirected (lab r = some r) and redirected (Rinf = r).
        have hMτpre : ∀ m ∈ Mτ, ∃ j ∈ Sτ, T j = some m := by
          intro m hm
          rw [hMτ] at hm
          rcases Finset.mem_insert.mp hm with rfl | hfil
          · refine ⟨firstProcessed σ Sτ i, numclust_rev_firstProcessed_mem σ _ i hSτne, ?_⟩
            have hsome : (T (firstProcessed σ Sτ i)).isSome = true :=
              (hSτmem _ (numclust_rev_firstProcessed_mem σ _ i hSτne)).2
            cases hTf : T (firstProcessed σ Sτ i) with
            | none => rw [hTf] at hsome; simp at hsome
            | some s =>
              have hri : riτ = s := by rw [hriτ, hTf]; simp
              rw [hri]
          · have him := (Finset.mem_filter.mp hfil).1
            obtain ⟨j, hjS, hjm⟩ := Finset.mem_image.mp him
            have hsome : (T j).isSome = true := (hSτmem j hjS).2
            cases hTj : T j with
            | none => rw [hTj] at hsome; simp at hsome
            | some s =>
              have hget : (T j).getD j = s := by rw [hTj]; simp
              have hms : m = s := hjm.symm.trans hget
              refine ⟨j, hjS, ?_⟩
              rw [hms]; exact hTj
        by_cases hri : r = i
        · rw [hri] at hlab
          rw [hI] at hlab
          simp only [Option.some.injEq] at hlab
          exact (hiM (by rw [← hlab]; exact hRinfmem)).elim
        · beta_reduce at hlab
          rw [if_neg hri] at hlab
          cases hlr : lab r with
          | none => rw [hlr] at hlab; simp at hlab
          | some a =>
            rw [hlr] at hlab
            simp only [Option.bind_some] at hlab
            beta_reduce at hlab
            by_cases haM : a ∈ Minf
            · -- Case B: the redirect fires, Rinf = r.
              rw [if_pos haM] at hlab
              simp only [Option.some.injEq] at hlab
              have hrm : r ∈ Minf := by rw [← hlab]; exact hRinfmem
              have hlabr : lab r = some r := hMroot r hrm
              have hTr_r : T r = some r := hKback r (Or.inl hlabr)
              by_cases hRinfMτ : Rinf ∈ Mτ
              · -- att29's chains: Rinf ∈ Mτ ⟹ Rτ = Rinf and Eτ = Rτ (no demotion).
                -- (1) Rinf is σ-eldest in Minf (firstProcessed minimality).
                have hRinfEldest : ∀ s ∈ Minf, (σ.symm s : ℕ) ≤ (σ.symm Rinf : ℕ) := by
                  intro s hs
                  have hle := numclust_rev_firstProcessed_le σ Minf
                    ((lab (firstProcessed σ (numclust_rev_neighSet Dm δ lab i) i)).getD
                      (firstProcessed σ (numclust_rev_neighSet Dm δ lab i) i)) hMne s hs
                  rw [hRinfdef]
                  exact hle
                -- (2) every T-root of an Sτ member is σ-dominated by Rinf: hREF keeps the
                -- plain label constant on τ-entries, hEl puts the τ-root below the plain
                -- root of the δ-close witness, and that plain root lies in Minf.
                have hrootle : ∀ j ∈ Sτ, (σ.symm ((T j).getD j) : ℕ) ≤ (σ.symm Rinf : ℕ) := by
                  intro j hjS
                  have hls : lab j = some ((lab j).getD j) := hlabjS j hjS
                  have hpjM : (lab j).getD j ∈ Minf := hrMS j hjS
                  have hiso : (T j).isSome = true := (hSτmem j hjS).2
                  cases hTj : T j with
                  | none => rw [hTj] at hiso; simp at hiso
                  | some s =>
                    have hlm : lab s = some ((lab j).getD j) := by
                      rw [← hREF j s hTj]; exact hls
                    have hle1 : (σ.symm s : ℕ) ≤ (σ.symm ((lab j).getD j) : ℕ) := hEl s _ hlm
                    show (σ.symm s : ℕ) ≤ (σ.symm Rinf : ℕ)
                    exact hle1.trans (hRinfEldest _ hpjM)
                have hMτle : ∀ m ∈ Mτ, (σ.symm m : ℕ) ≤ (σ.symm Rinf : ℕ) := by
                  intro m hm
                  obtain ⟨j, hjS, hjT⟩ := hMτpre m hm
                  have hle := hrootle j hjS
                  have hget : (T j).getD j = m := by rw [hjT]; simp
                  rw [hget] at hle
                  exact hle
                -- (3) Rτ = Rinf: Rinf ∈ Mτ and σ-dominates every Mτ member.
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
                -- (4) Eτ = Rτ: attained (Rinf's Sτ witness maps to Rτ after the merge)
                -- and σ-dominating (every post-merge Sτ root is Rτ or σ-below Rinf = Rτ).
                have hEτRτ : Eτ = Rτ := by
                  have hImgne : (Sτ.image (fun j => (hl2 j).getD j)).Nonempty :=
                    hSτne.image _
                  have hEmem : Eτ ∈ Sτ.image (fun j => (hl2 j).getD j) := by
                    rw [hEτ]; exact numclust_rev_firstProcessed_mem σ _ Rτ hImgne
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
                    have hle := numclust_rev_firstProcessed_le σ _ Rτ hImgne Rτ hatt
                    rw [hEτ]
                    exact hle
                  have hle2 : (σ.symm Eτ : ℕ) ≤ (σ.symm Rτ : ℕ) := by
                    obtain ⟨j, hjS, hym⟩ := Finset.mem_image.mp hEmem
                    obtain ⟨hjnei, hsome⟩ := hSτmem j hjS
                    cases hTj : T j with
                    | none => rw [hTj] at hsome; simp at hsome
                    | some x =>
                      have hl2j : (hl2 j).getD j = (if x ∈ Mτ then some Rτ else some x).getD j := by
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
                  have hEq : (σ.symm Eτ : ℕ) = (σ.symm Rτ : ℕ) := le_antisymm hle2 hle1
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
              · -- Rinf ∉ Mτ: T' keeps r's old root; the demotion branch also fixes r
                -- (r ≠ Rτ since Rτ ∈ Mτ).
                have hrMτ' : r ∉ Mτ := by
                  intro h
                  rw [← hlab] at h
                  exact hRinfMτ h
                have hrRτ : r ≠ Rτ := by
                  intro h
                  apply hrMτ'
                  rw [h]; exact hRτmem
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
              · -- entry-label constancy (hREF): r is the T-root of a δ-close j ∈ Sτ,
                -- so lab j = lab r = some r and (lab j).getD j = r ∈ Minf — absurd.
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
                  intro h
                  apply hrMτ
                  rw [h]; exact hRτmem
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
      · -- prominent case: prominent dth' r → T' r = some r.
        -- hA4 (at level t+1, k = t) gives (g i : EReal) ≤ dth r, so prominence forces
        -- the merge gap g r - g i ≥ τ both for the new death (r ∈ Minf.erase Rinf,
        -- dth' r = g i) and for an unchanged old death.
        obtain ⟨hgr, hTr_r, hrnei⟩ : (g i + τ : ℝ) ≤ g r ∧ T r = some r ∧ r ≠ i := by
          by_cases hrM : r ∈ Minf.erase Rinf
          · -- new death at level g i: (g i) + τ ≤ g r; r is a plain root, hence a τ-root.
            simp only [if_pos hrM] at hprom
            have hrm : r ∈ Minf := (Finset.mem_erase.mp hrM).2
            refine ⟨?_, hKback r (Or.inl (hMroot r hrm)), ?_⟩
            · have h1 := hprom.2.2
              rw [← EReal.coe_add] at h1
              exact EReal.coe_le_coe_iff.mp h1
            · intro hri
              rw [hri] at hrm
              exact hiM hrm
          · -- old death unchanged: prominent dth r; hA4 transports g i ≤ dth r.
            simp only [if_neg hrM] at hprom
            refine ⟨?_, hKback r (Or.inr ⟨hprom.1, hprom.2.1, hprom.2.2⟩), ?_⟩
            · have hgi : (g i : EReal) ≤ dth r := by
                have h2 := hA4 r ⟨hprom.1, hprom.2.1⟩ ⟨t, ht⟩ (Nat.lt_succ_self t)
                rw [show σ ⟨t, ht⟩ = i from by rw [← hiσ]; exact σ.apply_symm_apply i] at h2
                exact h2
              have h1 : (g i : EReal) + (τ : EReal) ≤ (g r : EReal) :=
                (add_le_add hgi (le_refl (τ : EReal))).trans hprom.2.2
              rw [← EReal.coe_add] at h1
              exact EReal.coe_le_coe_iff.mp h1
            · intro hri
              have hdthi : dth i = ⊥ := by
                by_contra hc
                have h3 := hI3 i hc
                rw [hlabi] at h3
                simp at h3
              rw [hri] at hprom
              exact hprom.1 hdthi
        by_cases hrMτ : r ∈ Mτ
        · -- r ∈ Mτ: the gap filter forces r = riτ, and riτ is then the σ-eldest member
          -- of Mτ (every other member has gap < τ, hence strictly smaller g), so Rτ = r;
          -- the demotion condition (g Rτ - g i < τ) cannot fire.
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
            intro h
            apply hrMτ
            rw [h]; exact hRτmem
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
    · -- C5 entry-fwd (repaired): forward characterization (shared with C6).
      exact hKfwdP
    · -- C6 entry-fwd (repaired): forward characterization (shared with C5).
      exact hKfwdP
    · -- C7 A4: recorded deaths dominate all future levels.
      -- dth' r = (g i : EReal) if r ∈ M∞.erase R∞ (a plain death), else dth r (unchanged).
      intro r hr k hk
      by_cases hd : r ∈ (numclust_rev_mergeSet σ Dm δ lab i).erase
          (numclust_rev_eldestRoot σ Dm δ lab i)
      · -- new death at level g i; monotone g∘σ gives g(σ k) ≤ g i for k < t.
        simp only [if_pos hd] at hr ⊢
        refine EReal.coe_le_coe_iff.mpr ?_
        exact hmono (σ k) i (by
          have hsk : (σ.symm (σ k) : ℕ) = k := by simp
          rw [hsk, hSymmI]; omega)
      · -- old death; unchanged, so A4(input) applies (k < t < t+1).
        simp only [if_neg hd] at hr ⊢
        exact hA4 r hr k (by omega)
    · -- CI-ELD: the plain entry's root stays σ-eldest through a merge.
      -- `Rinf = firstProcessed σ Minf` is σ-eldest among merge roots; `i` is
      -- σ-younger than every previously-processed root; the input elder rule
      -- `hEl` transports across the relabel, with `Rinf` topping every merged chain.
      intro v r h
      set Rinf := numclust_rev_eldestRoot σ Dm δ lab i with hRinfdef
      set Minf := numclust_rev_mergeSet σ Dm δ lab i with hMinfdef
      have hMroot : ∀ s : Fin n, s ∈ Minf → lab s = some s :=
        numclust_rev_mergeSet_root σ Dm δ lab i hS hI2
      have hMne : Minf.Nonempty := by rw [hMinfdef]; exact Finset.insert_nonempty _ _
      have hRinfmem : Rinf ∈ Minf := by
        simpa only [hRinfdef] using numclust_rev_firstProcessed_mem σ _ _ hMne
      have hRinfroot : lab Rinf = some Rinf := hMroot Rinf hRinfmem
      have hRinfEldest : ∀ s ∈ Minf, (σ.symm s : ℕ) ≤ (σ.symm Rinf : ℕ) := by
        intro s hs
        have hle := numclust_rev_firstProcessed_le σ Minf
          ((lab (firstProcessed σ (numclust_rev_neighSet Dm δ lab i) i)).getD
            (firstProcessed σ (numclust_rev_neighSet Dm δ lab i) i)) hMne s hs
        rw [hRinfdef]
        exact hle
      by_cases hvi : v = i
      · -- v = i: `lab' i = some Rinf`, so `r = Rinf`; `i` is σ-younger than `Rinf`
        -- (an old root: `lab Rinf = some Rinf` ⟹ `t+1 ≤ σ.symm Rinf` via `hI0`).
        beta_reduce at h
        rw [hvi, if_pos rfl] at h
        simp only [Option.some.injEq] at h
        rw [hvi, ← h]
        have hsome : (lab Rinf).isSome = true := by rw [hRinfroot]; simp
        have hge := (hI0 Rinf).mp hsome
        rw [hSymmI]
        omega
      · -- v ≠ i: `lab' v = Option.bind (lab v) …`; split on the old label.
        beta_reduce at h
        rw [if_neg hvi] at h
        cases hlv : lab v with
        | none => rw [hlv] at h; simp at h
        | some a =>
          rw [hlv] at h
          simp only [Option.bind_some] at h
          beta_reduce at h
          by_cases haM : a ∈ Minf
          · -- merged: `r = Rinf`; `σ.symm v ≤ σ.symm a` (hEl) ≤ `σ.symm Rinf` (eldest).
            rw [if_pos haM] at h
            simp only [Option.some.injEq] at h
            rw [← h]
            have hvel : (σ.symm v : ℕ) ≤ (σ.symm a : ℕ) := hEl v a hlv
            have hael : (σ.symm a : ℕ) ≤ (σ.symm Rinf : ℕ) := hRinfEldest a haM
            omega
          · -- unmerged: `r = a`; the input elder rule `hEl` closes directly.
            rw [if_neg haM] at h
            simp only [Option.some.injEq] at h
            rw [← h]
            exact hEl v a hlv

/-- The plain-sweep invariant for the joint fold (threshold induction). -/
private theorem numclust_rev_jointZero_fold (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ : ℝ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    ∀ j : ℕ, j ≤ n → numclust_rev_Inv g σ (n - j)
      ((((List.finRange n).reverse).take j).foldl
          (fun st k => numclust_rev_jointStep g Dm δ σ st (σ k))
          ((fun _ => none), (fun _ => ⊥), (fun _ => 0))).1
      ((((List.finRange n).reverse).take j).foldl
          (fun st k => numclust_rev_jointStep g Dm δ σ st (σ k))
          ((fun _ => none), (fun _ => ⊥), (fun _ => 0))).2.1
      ((((List.finRange n).reverse).take j).foldl
          (fun st k => numclust_rev_jointStep g Dm δ σ st (σ k))
          ((fun _ => none), (fun _ => ⊥), (fun _ => 0))).2.2 := by
  intro j hj
  induction j with
  | zero =>
    simp only [List.take_zero, List.foldl_nil]
    exact numclust_rev_Inv_init g σ
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
    refine numclust_rev_Inv_step g Dm δ σ hσ (n - (j+1)) (by omega) _ _ _ ?_
    simpa only [show n - (j+1) + 1 = n - j by omega] using ih (by omega)

/-- Core plain invariant over the coupled run, threshold induction. -/
private theorem numclust_rev_cRunInvCore_fold (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (δ τ : ℝ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    ∀ j : ℕ, j ≤ n → numclust_rev_InvCore g σ (n - j)
      ((((List.finRange n).reverse).take j).foldl
          (fun st k => numclust_rev_cstep n g Dm δ τ σ st (σ k))
          ((fun _ => none), (fun _ => none), (fun _ => ⊥))).2.1
      ((((List.finRange n).reverse).take j).foldl
          (fun st k => numclust_rev_cstep n g Dm δ τ σ st (σ k))
          ((fun _ => none), (fun _ => none), (fun _ => ⊥))).2.2 := by
  intro j hj
  have hcore : numclust_rev_InvCore g σ (n - j)
      ((((List.finRange n).reverse).take j).foldl
          (fun st k => numclust_rev_jointStep g Dm δ σ st (σ k))
          ((fun _ => none), (fun _ => ⊥), (fun _ => 0))).1
      ((((List.finRange n).reverse).take j).foldl
          (fun st k => numclust_rev_jointStep g Dm δ σ st (σ k))
          ((fun _ => none), (fun _ => ⊥), (fun _ => 0))).2.1 :=
    numclust_rev_InvCore_of_Inv g σ (n - j) _ _ _
      (numclust_rev_jointZero_fold n g Dm δ σ hσ j hj)
  have hproj := numclust_rev_cRun_snd (n := n) g Dm δ τ σ ((List.finRange n).reverse.take j)
    ((fun _ => none), (fun _ => none), (fun _ => ⊥))
  rw [congrArg Prod.fst hproj, congrArg Prod.snd hproj]
  exact numclust_rev_pairTriple_bridge g Dm δ σ ((List.finRange n).reverse.take j)
    (fun _ => none) (fun _ => ⊥) (fun _ => 0) ▸ hcore

/-- The coupled run satisfies the coupling invariant at threshold `0`. -/
private theorem numclust_rev_cRun_CI (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    numclust_rev_CI g τ σ 0 (numclust_rev_cRun n g Dm δ τ σ).1
      (numclust_rev_cRun n g Dm δ τ σ).2.1
      (numclust_rev_cRun n g Dm δ τ σ).2.2 := by
  have key : ∀ j : ℕ, j ≤ n → numclust_rev_CI g τ σ (n - j)
      ((((List.finRange n).reverse).take j).foldl
          (fun st k => numclust_rev_cstep n g Dm δ τ σ st (σ k))
          ((fun _ => none), (fun _ => none), (fun _ => ⊥))).1
      ((((List.finRange n).reverse).take j).foldl
          (fun st k => numclust_rev_cstep n g Dm δ τ σ st (σ k))
          ((fun _ => none), (fun _ => none), (fun _ => ⊥))).2.1
      ((((List.finRange n).reverse).take j).foldl
          (fun st k => numclust_rev_cstep n g Dm δ τ σ st (σ k))
          ((fun _ => none), (fun _ => none), (fun _ => ⊥))).2.2 := by
    intro j hj
    induction j with
    | zero =>
      simp only [List.take_zero, List.foldl_nil]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro v; simp
      · intro v r h; simp at h
      · intro v r h; simp at h
      · intro r h
        rcases h with h | ⟨h1, h2, h3⟩
        · simp at h
        · simp at h1
      · intro r h; simp at h
      · intro r h; simp at h
      · intro r h k _
        obtain ⟨h1, h2⟩ := h
        simp only [show ((fun _ : Fin n => (⊥ : EReal)) r) = ⊥ from rfl] at h1
        exact absurd rfl h1
      · -- CI-ELD: base state labels nothing, so `lab v = some r` is impossible.
        intro v r h; simp at h
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
      exact numclust_rev_CI_step g Dm hDm hDm0 δ τ hδ hτ σ hσ (n - (j+1)) (by omega)
        (σ ⟨n - (j+1), by omega⟩) (σ.symm_apply_apply _) _ _ _
        (by simpa only [show n - (j+1) + 1 = n - j by omega] using ih (by omega))
        (by simpa only [show n - (j+1) + 1 = n - j by omega] using
          numclust_rev_cRunInvCore_fold n g Dm δ τ σ hσ j (by omega))
  have hfinal : List.take n (List.finRange n).reverse = (List.finRange n).reverse := by
    apply List.take_of_length_le
    rw [List.length_reverse, List.length_finRange]
  simpa only [numclust_rev_cRun, hfinal, Nat.sub_self] using key n (Nat.le_refl n)

/-! ### (R) per-root characterization of final τ-roots (Claim K, backward direction) -/

private theorem numclust_rev_R_surv_immortal (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    ∀ r : Fin n, numclust_rev_barDeath n g Dm δ σ r = ⊤ → τ ≤ g r →
      r ∈ numclust_rev_survRoots n g Dm δ τ σ := by
  intro r htop hτr
  have hCI := numclust_rev_cRun_CI n g Dm hDm hDm0 δ τ hδ hτ σ hσ
  have hproj := numclust_rev_cRun_proj (n := n) g Dm δ τ σ
  have hInv := numclust_rev_jointRun_inv n g Dm δ σ hσ
  simp only [numclust_rev_barDeath] at htop
  have hlab : (numclust_rev_cRun n g Dm δ τ σ).2.1 r = some r := by
    have hlabj : (numclust_rev_cRun n g Dm δ τ σ).2.1
        = (numclust_rev_jointRun n g Dm δ σ).1 := congrArg Prod.fst hproj.2
    rw [hlabj]
    exact (hInv.2.1 r).mpr htop
  refine Finset.mem_filter.mpr ⟨by simp, ⟨⟨r, ?_⟩, hτr⟩⟩
  rw [← hproj.1]
  exact hCI.2.2.2.1 r (Or.inl hlab)

private theorem numclust_rev_R_surv_prominent (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    ∀ r : Fin n, τ ≤ g r →
      numclust_rev_barDeath n g Dm δ σ r ≠ ⊥ → numclust_rev_barDeath n g Dm δ σ r ≠ ⊤ →
        numclust_rev_barDeath n g Dm δ σ r + (τ : EReal) ≤ (g r : EReal) →
          r ∈ numclust_rev_survRoots n g Dm δ τ σ := by
  intro r hτr hne1 hne2 hle
  have hCI := numclust_rev_cRun_CI n g Dm hDm hDm0 δ τ hδ hτ σ hσ
  have hproj := numclust_rev_cRun_proj (n := n) g Dm δ τ σ
  have hdth : (numclust_rev_cRun n g Dm δ τ σ).2.2
      = (numclust_rev_jointRun n g Dm δ σ).2.1 := congrArg Prod.snd hproj.2
  simp only [numclust_rev_barDeath] at hne1 hne2 hle
  refine Finset.mem_filter.mpr ⟨by simp, ⟨⟨r, ?_⟩, hτr⟩⟩
  rw [← hproj.1]
  refine hCI.2.2.2.1 r (Or.inr ⟨?_, ?_, ?_⟩)
  · rw [congrFun hdth r]; exact hne1
  · rw [congrFun hdth r]; exact hne2
  · rw [congrFun hdth r]; exact hle

/-- Every non-infinite EReal value is the coercion of a real. -/
private theorem numclust_rev_existsReal {x : EReal} (h1 : x ≠ ⊥) (h2 : x ≠ ⊤) :
    ∃ a : ℝ, x = ((a : EReal)) := by
  have hmem : x ∈ Set.range (fun a : ℝ => ((a : EReal))) := by
    rw [EReal.range_coe]
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1, h2⟩
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, ha.symm⟩

/-! ### (E) fiber-size bound -/

private theorem numclust_rev_E_fiber_bound (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    ∀ p : EReal × EReal, p.2 ≤ p.1 - (τ : EReal) → (τ : EReal) ≤ p.1 →
      ripsBarcode g Dm δ σ p
        ≤ (((numclust_rev_survRoots n g Dm δ τ σ).filter
              (fun r => numclust_rev_barPair n g Dm δ σ r = p)).card : ℕ∞) := by
  rintro ⟨b, d⟩ hp2 hp1
  by_cases hdb : d = ⊥
  · subst hdb
    rw [numclust_rev_BD_immortal n g Dm δ σ hσ b]
    rw [ENat.natCast_le_natCast]
    apply Finset.card_le_card
    intro r hr
    rw [Finset.mem_filter] at hr ⊢
    obtain ⟨-, htop, hgb⟩ := hr
    refine ⟨?_, ?_⟩
    · exact numclust_rev_R_surv_immortal n g Dm hDm hDm0 δ τ hδ hτ σ hσ r htop
        (EReal.coe_le_coe_iff.mp (by rw [hgb]; exact hp1))
    · simp [numclust_rev_barPair, htop, hgb]
  · by_cases hdt : d = ⊤
    · subst hdt
      rw [numclust_rev_BD_top n g Dm δ σ hσ b]
      simp
    · rw [numclust_rev_BD_real n g Dm δ σ hσ b d hdb hdt]
      rw [ENat.natCast_le_natCast]
      apply Finset.card_le_card
      intro r hr
      rw [Finset.mem_filter] at hr ⊢
      obtain ⟨-, hdbd, hgb, hlt⟩ := hr
      have harith : d + (τ : EReal) ≤ b := by
        have := (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot τ))
          (Or.inl (EReal.coe_ne_top τ))).mp hp2
        simpa using this
      refine ⟨?_, ?_⟩
      · exact numclust_rev_R_surv_prominent n g Dm hDm hDm0 δ τ hδ hτ σ hσ r
          (EReal.coe_le_coe_iff.mp (by rw [hgb]; exact hp1)) (by rw [hdbd]; exact hdb)
          (by rw [hdbd]; exact hdt) (by rw [hdbd, hgb]; exact harith)
      · simp [numclust_rev_barPair, hdbd, hgb, hdt]

/-! ### (P) pairing: region copies ↦ distinct surviving roots -/

/-- The fiber above a region point. -/
private abbrev numclust_rev_fiber (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ τ : ℝ)
    (σ : Fin n ≃ Fin n) (p : EReal × EReal) : Finset (Fin n) :=
  (numclust_rev_survRoots n g Dm δ τ σ).filter (fun r => numclust_rev_barPair n g Dm δ σ r = p)

private theorem numclust_rev_P_region_inj (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    ∃ f : ↥(numclust_rev_regionSet n g Dm δ τ σ) → Fin n,
      Function.Injective f ∧
      ∀ q : ↥(numclust_rev_regionSet n g Dm δ τ σ),
        f q ∈ numclust_rev_survRoots n g Dm δ τ σ ∧
          numclust_rev_barPair n g Dm δ σ (f q) = (q : (EReal × EReal) × ℕ).1 := by
  classical
  have hE := numclust_rev_E_fiber_bound n g Dm hDm hDm0 δ τ hδ hτ σ hσ
  have hcard : ∀ q : ↥(numclust_rev_regionSet n g Dm δ τ σ),
      q.1.2 < (numclust_rev_fiber n g Dm δ τ σ q.1.1).card := by
    intro q
    obtain ⟨p, hp⟩ := q
    obtain ⟨⟨b, d⟩, k⟩ := p
    exact ENat.natCast_lt_natCast.mp (lt_of_lt_of_le hp.1 (hE (b, d) hp.2.1 hp.2.2))
  let L : ↥(numclust_rev_regionSet n g Dm δ τ σ) → List (Fin n) :=
    fun q => (numclust_rev_fiber n g Dm δ τ σ q.1.1).sort (fun a b => a ≤ b)
  let f : ↥(numclust_rev_regionSet n g Dm δ τ σ) → Fin n :=
    fun q => (L q)[q.1.2]'(by rw [Finset.length_sort]; exact hcard q)
  have hfnodup : ∀ q : ↥(numclust_rev_regionSet n g Dm δ τ σ), (L q).Nodup :=
    fun q => Finset.sort_nodup _ _
  have hflen : ∀ q : ↥(numclust_rev_regionSet n g Dm δ τ σ), (L q).length =
      (numclust_rev_fiber n g Dm δ τ σ q.1.1).card := fun q => Finset.length_sort _
  have hmem : ∀ q : ↥(numclust_rev_regionSet n g Dm δ τ σ),
      f q ∈ numclust_rev_fiber n g Dm δ τ σ q.1.1 := by
    intro q
    exact Finset.mem_sort (· ≤ ·) |>.mp (List.getElem_mem (by rw [hflen q]; exact hcard q))
  have hsurv : ∀ q : ↥(numclust_rev_regionSet n g Dm δ τ σ),
      f q ∈ numclust_rev_survRoots n g Dm δ τ σ ∧
        numclust_rev_barPair n g Dm δ σ (f q) = q.1.1 := fun q =>
    Finset.mem_filter.mp (hmem q)
  refine ⟨f, ?_, hsurv⟩
  intro q q' h
  have hpair : ∀ q : ↥(numclust_rev_regionSet n g Dm δ τ σ),
      numclust_rev_barPair n g Dm δ σ (f q) = q.1.1 := fun q => (Finset.mem_filter.mp (hmem q)).2
  have hq : q.1.1 = q'.1.1 := by rw [← hpair q, ← hpair q', h]
  have hidx : ∀ q : ↥(numclust_rev_regionSet n g Dm δ τ σ),
      List.idxOf (f q) ((numclust_rev_fiber n g Dm δ τ σ q.1.1).sort (fun a b => a ≤ b)) = q.1.2 := by
    intro q
    have hfe : f q = ((numclust_rev_fiber n g Dm δ τ σ q.1.1).sort (fun a b => a ≤ b))[q.1.2]'
        (by rw [Finset.length_sort]; exact hcard q) := rfl
    rw [hfe]
    exact List.Nodup.idxOf_getElem (Finset.sort_nodup _ (fun a b : Fin n => a ≤ b)) q.1.2
      (by rw [Finset.length_sort]; exact hcard q)
  have hk : q.1.2 = q'.1.2 := by
    have h1 := hidx q
    have h2 : List.idxOf (f q') ((numclust_rev_fiber n g Dm δ τ σ q.1.1).sort (fun a b => a ≤ b))
        = q'.1.2 := by
      rw [hq]
      exact hidx q'
    rw [← h1, h, h2]
  exact Subtype.ext (Prod.ext hq hk)
/-! ### (A) encard assembly -/

private theorem numclust_rev_A_encard_le (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    (numclust_rev_regionSet n g Dm δ τ σ).encard ≤ (numClusters g Dm δ τ σ : ℕ∞) := by
  obtain ⟨f, hf_inj, hf_prop⟩ := numclust_rev_P_region_inj n g Dm hDm hDm0 δ τ hδ hτ σ hσ
  calc (numclust_rev_regionSet n g Dm δ τ σ).encard
      = (Set.univ : Set ↥(numclust_rev_regionSet n g Dm δ τ σ)).encard :=
        Set.encard_congr (Equiv.symm (Equiv.Set.univ ↥(numclust_rev_regionSet n g Dm δ τ σ)))
    _ ≤ (↑(numclust_rev_survRoots n g Dm δ τ σ) : Set (Fin n)).encard := by
        apply Set.encard_le_encard_of_injOn
        · intro q _
          exact (hf_prop q).1
        · intro q _ q' _ h
          exact hf_inj h
    _ = ((numclust_rev_survRoots n g Dm δ τ σ).card : ℕ∞) :=
        Set.encard_coe_eq_coe_finsetCard _
    _ = (numClusters g Dm δ τ σ : ℕ∞) := rfl

/-- Reverse inequality: every barcode copy with prominence at least `τ` and birth at least
`τ` is realized by a distinct cluster output by the τ-thresholded union-find Procedure 1. -/
theorem solution
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ)
    (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < ripsBarcode g Dm δ σ q.1 ∧
        q.1.2 ≤ q.1.1 - (τ : EReal) ∧ (τ : EReal) ≤ q.1.1}.encard
      ≤ (numClusters g Dm δ τ σ : ℕ∞) :=
  numclust_rev_A_encard_le n g Dm hDm hDm0 δ τ hδ hτ σ hσ

end
