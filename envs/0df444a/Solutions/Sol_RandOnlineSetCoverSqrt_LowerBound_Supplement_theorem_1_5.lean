-- Prove2me | solution 1 for RandOnlineSetCoverSqrt.LowerBound.Supplement.theorem_1_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T19:31:34.175158+00:00
-- url     : https://prove2.me/submissions/f521f009-daea-40e0-8e5e-b9f21f8a6dc9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Supplement_Memory
import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Supplement_BinomialRatio
import Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_lemma_3_1
import Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_Supplement_lemma_3_4
import Theorems.Thm_RandOnlineSetCoverSqrt_LowerBound_Supplement_lemma_6_4
import Theorems.Thm_Gronemeier_oneWay_disjointness_lower_bound

section
set_option autoImplicit false

namespace RandOnlineSetCoverSqrt.Dev.T15
open RandOnlineSetCoverSqrt.LowerBound RandOnlineSetCoverSqrt.LowerBound.Supplement

/-! ### Runs of a memory-bounded algorithm -/

section Run
variable {m S : ℕ} (A : MemAlg m S)

/-- One arrival, as a map on laws of configurations. -/
noncomputable def stepF (μ : PMF (MemConfig m S)) (u : Element m) : PMF (MemConfig m S) :=
  μ.bind fun x => A.arrive x u

/-- Running a list from a mixed start is the mixture of runs from point starts. -/
theorem foldl_eq_bind (L : List (Element m)) (μ : PMF (MemConfig m S)) :
    L.foldl (stepF A) μ = μ.bind (fun x => L.foldl (stepF A) (PMF.pure x)) := by
  induction L generalizing μ with
  | nil => simp
  | cons u L ih =>
    simp only [List.foldl_cons]
    rw [ih (stepF A μ u)]
    simp only [stepF, PMF.bind_bind, PMF.pure_bind]
    congr 1
    funext x
    rw [ih (A.arrive x u)]

/-- Coverage invariant: on a run whose feasibility flag is still `true`, every request seen so
far meets the purchased labels. -/
theorem foldl_cover (μ : PMF (MemConfig m S)) (B : List (Element m)) :
    ∀ x, B.foldl (stepF A) μ x ≠ 0 → x.2.2 = true → ∀ u ∈ B, (x.2.1 ∩ u.val).Nonempty := by
  induction B using List.reverseRecOn with
  | nil => intro x _ _ u hu; simp at hu
  | append_singleton B u ih =>
    intro x hx h2 v hv
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← PMF.mem_support_iff, stepF,
      PMF.mem_support_bind_iff] at hx
    obtain ⟨x₁, hx₁, hx⟩ := hx
    rw [MemAlg.arrive, PMF.support_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨h21, h22⟩ := h2
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨z, hz⟩ := ih x₁ ((PMF.mem_support_iff _ _).mp hx₁) h21 v hv
      exact ⟨z, Finset.mem_inter.2 ⟨Finset.mem_union_left _ (Finset.mem_inter.1 hz).1,
        (Finset.mem_inter.1 hz).2⟩⟩
    · simp only [List.mem_singleton] at hv
      subst hv
      exact h22

/-- Transport of the multi-player protocol: playing the players' batches one after another
on the encoded states is the encoded run of the concatenated batches. -/
theorem protocol_foldl {q K : ℕ} (e : MemConfig m S ≃ Fin K) (bt : Fin q → List (Element m))
    (L : List (Fin q)) (μ : PMF (MemConfig m S)) :
    L.foldl (fun ν i => ν.bind fun s => ((bt i).foldl (stepF A) (PMF.pure (e.symm s))).map e)
        (μ.map e)
      = ((L.flatMap bt).foldl (stepF A) μ).map e := by
  induction L generalizing μ with
  | nil => simp
  | cons i L ih =>
    rw [List.foldl_cons, List.flatMap_cons, List.foldl_append, ← ih]
    congr 1
    rw [PMF.bind_map, foldl_eq_bind A (bt i) μ, PMF.map_bind]
    congr 1
    funext x
    simp

end Run

theorem map_equiv_apply {α β : Type*} (e : α ≃ β) (μ : PMF α) (x : α) :
    (μ.map e) (e x) = μ x := by
  rw [PMF.map_apply, tsum_eq_single x]
  · simp
  · intro y hy
    rw [if_neg]
    intro h
    exact hy (e.injective h).symm

theorem sum_out {m S K : ℕ} (e : MemConfig m S ≃ Fin K) (μ : PMF (MemConfig m S)) (r : ℕ)
    (b : Bool) :
    (∑ s, if decide ((e.symm s).2.1.card ≤ r) = b then (μ.map e) s else 0) =
      ∑ x, if decide (x.2.1.card ≤ r) = b then μ x else 0 := by
  rw [← e.sum_comp]
  congr 1
  funext x
  rw [Equiv.symm_apply_apply, map_equiv_apply]

theorem sum_ite_ne_top {α : Type*} [Fintype α] (μ : PMF α) (P : α → Prop) [DecidablePred P] :
    (∑ x, if P x then μ x else 0) ≠ ⊤ := by
  refine ENNReal.sum_ne_top.2 fun x _ => ?_
  split_ifs
  · exact PMF.apply_ne_top μ x
  · exact ENNReal.zero_ne_top

/-- Markov's inequality for the number of purchased labels. -/
theorem tail_toReal {m S : ℕ} (μ : PMF (MemConfig m S)) (r : ℕ) :
    (∑ x, if decide (x.2.1.card ≤ r) = false then μ x else 0).toReal ≤
      (∑ x, (μ x).toReal * (x.2.1.card : ℝ)) / (r + 1) := by
  rw [ENNReal.toReal_sum (fun x _ => by
    split_ifs
    · exact PMF.apply_ne_top μ x
    · exact ENNReal.zero_ne_top), Finset.sum_div]
  apply Finset.sum_le_sum
  intro x _
  have h0 := ENNReal.toReal_nonneg (a := μ x)
  split_ifs with h
  · simp only [decide_eq_false_iff_not, not_le] at h
    have hc : ((r : ℝ) + 1) ≤ x.2.1.card := by exact_mod_cast h
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · simp only [ENNReal.toReal_zero]
    positivity

theorem ennreal_le_third {s : ENNReal} (hs : s ≠ ⊤) (h : s.toReal ≤ 1 / 3) : s ≤ 1 / 3 := by
  rw [← ENNReal.ofReal_toReal hs]
  calc ENNReal.ofReal s.toReal ≤ ENNReal.ofReal (1 / 3) := ENNReal.ofReal_le_ofReal h
    _ = 1 / 3 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      simp

theorem logb_card (m S : ℕ) :
    Real.logb 2 (Fintype.card (MemConfig m S) : ℝ) = (S : ℝ) + m + 1 := by
  have h : (Fintype.card (MemConfig m S) : ℝ) = (2 : ℝ) ^ (S + m + 1) := by
    simp only [MemConfig, Fintype.card_prod, Fintype.card_fin, Fintype.card_finset,
      Fintype.card_bool]
    push_cast
    ring
  rw [h, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  push_cast
  ring

/-! ### Batches, players' families, coverage -/

theorem coversBatch_iff {m : ℕ} {X : Finset (Fin m)} {B : List (Element m)} :
    CoversBatch X B ↔ ∀ u ∈ B, (X ∩ u.val).Nonempty := by
  unfold CoversBatch RandOnlineSetCover.InfoLB.Covers incidences
  simp

theorem listOptNat_le {m : ℕ} {B : List (Element m)} {X : Finset (Fin m)}
    (h : CoversBatch X B) : listOptNat B ≤ X.card := by
  unfold listOptNat RandOnlineSetCover.InfoLB.listOpt
  apply ENat.toNat_le_of_le_natCast
  exact iInf_le (fun C : {C : Finset (Fin m) //
    RandOnlineSetCover.InfoLB.Covers (incidences B) C} => (C.val.card : ℕ∞)) ⟨X, h⟩

open Classical in
/-- The forcing batch of `D` given by Lemma 3.1 (by choice). -/
noncomputable def bat {m : ℕ} (r : ℕ) (D : Family m) : List (Element m) :=
  if h : D.Nonempty ∧ (∀ W ∈ D, W.Nonempty) ∧ 1 ≤ r then
    Classical.choose (lemma_3_1 D h.1 h.2.1 r h.2.2) else []

theorem bat_forcing {m r : ℕ} {D : Family m} (h1 : D.Nonempty) (h2 : ∀ W ∈ D, W.Nonempty)
    (h3 : 1 ≤ r) : Forcing r D (bat r D) := by
  have h : D.Nonempty ∧ (∀ W ∈ D, W.Nonempty) ∧ 1 ≤ r := ⟨h1, h2, h3⟩
  unfold bat
  rw [dif_pos h]
  exact (Classical.choose_spec (lemma_3_1 D h.1 h.2.1 r h.2.2)).1

theorem bat_ne_nil {m r k : ℕ} {D : Family m} {B : List (Element m)} (hF : Forcing r D B)
    (hk : ∀ W ∈ D, W.card = k) (hk1 : 1 ≤ k) : B ≠ [] := by
  rintro rfl
  obtain ⟨W, hW, hsub⟩ := (hF ∅ (by simp)).1 (coversBatch_iff.2 (by simp))
  have h1 := hk W hW
  rw [Finset.subset_empty.mp hsub, Finset.card_empty] at h1
  omega

/-- Player `i`'s family: its own private candidate `V i` and the shared candidates `W s`,
`s ∈ T`. -/
def fam {m N q : ℕ} (W : Fin N → Candidate m) (V : Fin q → Candidate m) (T : Finset (Fin N))
    (i : Fin q) : Family m :=
  insert (V i) (T.image W)

theorem mem_fam {m N q : ℕ} {W : Fin N → Candidate m} {V : Fin q → Candidate m}
    {T : Finset (Fin N)} {i : Fin q} {U : Candidate m} :
    U ∈ fam W V T i ↔ U = V i ∨ ∃ s ∈ T, W s = U := by
  unfold fam
  rw [Finset.mem_insert, Finset.mem_image]

theorem fam_sub {m N q : ℕ} {C : Family m} {W : Fin N → Candidate m} {V : Fin q → Candidate m}
    (hWC : ∀ s, W s ∈ C) (hVC : ∀ i, V i ∈ C) {T : Finset (Fin N)} {i : Fin q}
    {U : Candidate m} (hU : U ∈ fam W V T i) : U ∈ C := by
  rcases mem_fam.1 hU with h | ⟨s, -, h⟩
  · rw [h]; exact hVC i
  · rw [← h]; exact hWC s

theorem fam_forcing {m N q k r : ℕ} {C : Family m} (hUE : UnionExpanding k q r C)
    (W : Fin N → Candidate m) (V : Fin q → Candidate m) (hWC : ∀ s, W s ∈ C)
    (hVC : ∀ i, V i ∈ C) (T : Finset (Fin N)) (i : Fin q) :
    Forcing r (fam W V T i) (bat r (fam W V T i)) := by
  obtain ⟨hk1, hkr, -, -, hcardk, -⟩ := hUE
  refine bat_forcing ⟨V i, mem_fam.2 (Or.inl rfl)⟩ ?_ (le_trans hk1 hkr)
  intro U hU
  rw [← Finset.card_pos, hcardk U (fam_sub hWC hVC hU)]
  omega

/-- Disjoint inputs: with probability one the algorithm buys more than `r` labels. -/
theorem no_small_cover {m S : ℕ} (A : MemAlg m S) (hA : A.IsValid) {N q k r : ℕ}
    {C : Family m} (hUE : UnionExpanding k q r C)
    (W : Fin N → Candidate m) (V : Fin q → Candidate m) (hW : Function.Injective W)
    (hV : Function.Injective V) (hWV : ∀ s i, W s ≠ V i) (hWC : ∀ s, W s ∈ C)
    (hVC : ∀ i, V i ∈ C)
    (Sp : Fin q → Finset (Fin N)) (hSp : ∀ i j, i ≠ j → Disjoint (Sp i) (Sp j))
    (x : MemConfig m S)
    (hx : ((List.finRange q).flatMap fun i => bat r (fam W V (Sp i) i)).foldl (stepF A)
      (A.init.map fun y => (y.1, y.2, true)) x ≠ 0) :
    r < x.2.1.card := by
  classical
  by_contra hle
  push_neg at hle
  have hval := hA _ x hx
  have hcov := foldl_cover A (A.init.map fun y => (y.1, y.2, true)) _ x hx hval
  have hfor : ∀ i, ∃ U ∈ fam W V (Sp i) i, U ⊆ x.2.1 := by
    intro i
    refine ((fam_forcing hUE W V hWC hVC (Sp i) i) x.2.1 hle).1 (coversBatch_iff.2 ?_)
    intro u hu
    exact hcov u (List.mem_flatMap.2 ⟨i, List.mem_finRange i, hu⟩)
  choose U hUmem hUsub using hfor
  have hUinj : Function.Injective U := by
    intro i j hij
    by_contra hne
    rcases mem_fam.1 (hUmem i) with hi | ⟨s, hs, hi⟩ <;>
      rcases mem_fam.1 (hUmem j) with hj | ⟨t, ht, hj⟩
    · exact hne (hV (hi.symm.trans (hij.trans hj)))
    · exact hWV t i (hj.trans (hij.symm.trans hi))
    · exact hWV s j (hi.trans (hij.trans hj))
    · have hst : s = t := hW (hi.trans (hij.trans hj.symm))
      subst hst
      exact Finset.disjoint_left.mp (hSp i j hne) hs ht
  have hUC : ∀ i, U i ∈ C := fun i => fam_sub hWC hVC (hUmem i)
  have hlt := hUE.2.2.2.2.2 (Finset.univ.image U)
    (by
      intro W' hW'
      simp only [Finset.mem_image] at hW'
      obtain ⟨i, -, rfl⟩ := hW'
      exact hUC i)
    (by rw [Finset.card_image_of_injective _ hUinj, Finset.card_univ, Fintype.card_fin])
  have hsub : (Finset.univ.image U).biUnion id ⊆ x.2.1 := by
    intro y hy
    simp only [Finset.mem_biUnion, Finset.mem_image, id] at hy
    obtain ⟨_, ⟨i, -, rfl⟩, hy⟩ := hy
    exact hUsub i hy
  have := Finset.card_le_card hsub
  omega

/-- Intersecting inputs: the common candidate covers every batch. -/
theorem common_cover {m N q k r : ℕ} {C : Family m} (hUE : UnionExpanding k q r C)
    (W : Fin N → Candidate m) (V : Fin q → Candidate m) (hWC : ∀ s, W s ∈ C)
    (hVC : ∀ i, V i ∈ C) (Sp : Fin q → Finset (Fin N)) (s₀ : Fin N) (hs₀ : ∀ i, s₀ ∈ Sp i) :
    ((List.finRange q).flatMap fun i => bat r (fam W V (Sp i) i)) ≠ [] ∧
      listOptNat ((List.finRange q).flatMap fun i => bat r (fam W V (Sp i) i)) ≤ k := by
  have hF : ∀ i, Forcing r (fam W V (Sp i) i) (bat r (fam W V (Sp i) i)) :=
    fun i => fam_forcing hUE W V hWC hVC (Sp i) i
  obtain ⟨hk1, hkr, -, hq2, hcardk, -⟩ := hUE
  constructor
  · have h0 : (⟨0, by omega⟩ : Fin q) ∈ List.finRange q := List.mem_finRange _
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _
      (bat_ne_nil (hF ⟨0, by omega⟩) (fun U hU => hcardk U (fam_sub hWC hVC hU)) hk1)
    exact List.ne_nil_of_mem (List.mem_flatMap.2 ⟨_, h0, hu⟩)
  · have hcov : CoversBatch (W s₀)
        ((List.finRange q).flatMap fun i => bat r (fam W V (Sp i) i)) := by
      rw [coversBatch_iff]
      intro u hu
      obtain ⟨i, -, hu⟩ := List.mem_flatMap.1 hu
      have h := (hF i (W s₀) (by rw [hcardk _ (hWC s₀)]; exact hkr)).2
        ⟨W s₀, mem_fam.2 (Or.inr ⟨s₀, hs₀ i, rfl⟩), subset_rfl⟩
      exact coversBatch_iff.1 h u hu
    have := listOptNat_le hcov
    rwa [hcardk _ (hWC s₀)] at this

/-- The reduction: a memory-`S` algorithm that is `ρ`-competitive gives a one-way protocol for
`q`-party disjointness on `N` coordinates with `S + m + 1` bits, so Gronemeier's bound applies. -/
theorem protocol_lb {m S : ℕ} (A : MemAlg m S) (c₀ : ℝ)
    (hG : ∀ q N K : ℕ, 2 ≤ q →
      ∀ (init : PMF (Fin K)) (step : Fin q → Fin K → Finset (Fin N) → PMF (Fin K))
        (out : Fin K → Bool),
      (∀ Sp : Fin q → Finset (Fin N), (∀ i j, i ≠ j → Disjoint (Sp i) (Sp j)) →
        (∑ s, if out s = true then
          ((List.finRange q).foldl (fun μ i => μ.bind fun s => step i s (Sp i)) init) s
          else 0) ≤ 1 / 3) →
      (∀ Sp : Fin q → Finset (Fin N), ∀ x : Fin N, (∀ i, x ∈ Sp i) →
        (∀ i j, i ≠ j → Disjoint ((Sp i).erase x) ((Sp j).erase x)) →
        (∑ s, if out s = false then
          ((List.finRange q).foldl (fun μ i => μ.bind fun s => step i s (Sp i)) init) s
          else 0) ≤ 1 / 3) →
      c₀ * (N : ℝ) ≤ (q : ℝ) ^ 2 * Real.logb 2 (K : ℝ))
    (hA : A.IsValid) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hcon : ∀ B : List (Element m), B ≠ [] → A.expectedCost B < ρ * (listOptNat B : ℝ))
    {k r q N : ℕ} {C : Family m} (hUE : UnionExpanding k q r C) (hcard : C.card = N + q)
    (hkr3 : 3 * ρ * k < r + 1) :
    c₀ * (N : ℝ) ≤ (q : ℝ) ^ 2 * ((S : ℝ) + m + 1) := by
  classical
  have hq2 : 2 ≤ q := hUE.2.2.2.1
  let e' := Finset.equivFinOfCardEq hcard
  let φ : Fin (N + q) → Candidate m := fun j => (e'.symm j).val
  have hφ : Function.Injective φ := fun i j h => e'.symm.injective (Subtype.ext h)
  have hφC : ∀ j, φ j ∈ C := fun j => (e'.symm j).2
  let W : Fin N → Candidate m := fun s => φ (Fin.castAdd q s)
  let V : Fin q → Candidate m := fun i => φ (Fin.natAdd N i)
  have hW : Function.Injective W := by
    intro i j h
    have h' := hφ h
    rw [Fin.ext_iff] at h'
    simp only [Fin.val_castAdd] at h'
    exact Fin.ext h'
  have hV : Function.Injective V := by
    intro i j h
    exact (Fin.natAdd_inj N).1 (hφ h)
  have hWV : ∀ s i, W s ≠ V i := by
    intro s i h
    have h' := hφ h
    rw [Fin.ext_iff] at h'
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    have := s.isLt
    omega
  have hWC : ∀ s, W s ∈ C := fun s => hφC _
  have hVC : ∀ i, V i ∈ C := fun i => hφC _
  let e := Fintype.equivFin (MemConfig m S)
  have key := hG q N (Fintype.card (MemConfig m S)) hq2
    ((A.init.map fun y => (y.1, y.2, true)).map e)
    (fun i s T => ((bat r (fam W V T i)).foldl (stepF A) (PMF.pure (e.symm s))).map e)
    (fun s => decide ((e.symm s).2.1.card ≤ r)) ?_ ?_
  · rw [logb_card] at key
    exact key
  · intro Sp hSp
    have hf := protocol_foldl A e (fun i => bat r (fam W V (Sp i) i)) (List.finRange q)
      (A.init.map fun y => (y.1, y.2, true))
    beta_reduce at hf ⊢
    rw [hf, sum_out]
    rw [Finset.sum_eq_zero]
    · simp
    intro x _
    split_ifs with h
    · by_contra hx
      have := no_small_cover A hA hUE W V hW hV hWV hWC hVC Sp hSp x hx
      simp only [decide_eq_true_eq] at h
      omega
    · rfl
  · intro Sp s₀ hs₀ _
    have hf := protocol_foldl A e (fun i => bat r (fam W V (Sp i) i)) (List.finRange q)
      (A.init.map fun y => (y.1, y.2, true))
    beta_reduce at hf ⊢
    rw [hf, sum_out]
    obtain ⟨hne, hopt⟩ := common_cover hUE W V hWC hVC Sp s₀ hs₀
    have hE := hcon _ hne
    apply ennreal_le_third (sum_ite_ne_top _ _)
    refine le_trans (tail_toReal _ r) ?_
    have hopt' : (listOptNat ((List.finRange q).flatMap fun i => bat r (fam W V (Sp i) i)) : ℝ)
        ≤ k := by exact_mod_cast hopt
    have h1 := mul_le_mul_of_nonneg_left hopt' hρ
    have hE' : (∑ x, ((((List.finRange q).flatMap fun i => bat r (fam W V (Sp i) i)).foldl
        (stepF A) (A.init.map fun y => (y.1, y.2, true))) x).toReal * (x.2.1.card : ℝ)) <
        ρ * k := lt_of_lt_of_le hE h1
    rw [div_le_iff₀ (by positivity)]
    linarith

/-! ### Analysis -/

theorem binEnt_bound {α : ℝ} (hα : 1 ≤ α) :
    α * Real.binEntropy (1 / α) ≤ Real.log α + 1 := by
  have hα0 : 0 < α := by linarith
  set p := 1 / α with hp
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hα0]; exact hα
  have key : (1 - p) * Real.log (1 - p)⁻¹ ≤ p := by
    rcases eq_or_lt_of_le hp1 with h | h
    · rw [h]; simp
    · have h1 : 0 < 1 - p := by linarith
      have := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
      calc (1 - p) * Real.log (1 - p)⁻¹ ≤ (1 - p) * ((1 - p)⁻¹ - 1) :=
            mul_le_mul_of_nonneg_left this h1.le
        _ = p := by rw [mul_sub, mul_inv_cancel₀ h1.ne']; ring
  unfold Real.binEntropy
  have hpinv : p⁻¹ = α := by rw [hp, one_div, inv_inv]
  have hαp : α * p = 1 := by rw [hp, mul_one_div_cancel hα0.ne']
  rw [hpinv]
  calc α * (p * Real.log α + (1 - p) * Real.log (1 - p)⁻¹)
      = (α * p) * Real.log α + α * ((1 - p) * Real.log (1 - p)⁻¹) := by ring
    _ ≤ (α * p) * Real.log α + α * p := by gcongr
    _ = Real.log α + 1 := by rw [hαp]; ring

theorem b_bounds {α : ℝ} (hα : 1 ≤ α) :
    1 / (Real.exp 1 * α) ≤ Real.exp (-(α * Real.binEntropy (1 / α))) ∧
      Real.exp (-(α * Real.binEntropy (1 / α))) ≤ 1 := by
  have hα0 : 0 < α := by linarith
  constructor
  · have h := binEnt_bound hα
    have : 1 / (Real.exp 1 * α) = Real.exp (-(Real.log α + 1)) := by
      rw [Real.exp_neg, Real.exp_add, Real.exp_log hα0]; ring
    rw [this]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [Real.exp_le_one_iff]
    have : 0 ≤ Real.binEntropy (1 / α) :=
      Real.binEntropy_nonneg (by positivity) (by rw [div_le_one hα0]; exact hα)
    nlinarith

theorem half_le_log_one_add {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1) : b / 2 ≤ Real.log (1 + b) := by
  have hpos : 0 < 1 + b := by linarith
  have := Real.one_sub_inv_le_log_of_pos hpos
  have h2 : b / 2 ≤ 1 - (1 + b)⁻¹ := by
    rw [inv_eq_one_div, one_sub_div hpos.ne', div_le_div_iff₀ (by norm_num) hpos]
    nlinarith
  linarith

theorem alpha_ge_one {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : ⌈1 / c ^ 2⌉₊ ≤ m) (hm3 : 3 ≤ m) :
    1 ≤ 3 * (c * ((m : ℝ) / Real.log m)) := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have hm0 : (0 : ℝ) < m := by linarith
  have hΛ : 0 < Real.log m := Real.log_pos (by linarith)
  have h1 : 1 / c ^ 2 ≤ (m : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
  rw [div_le_iff₀ (by positivity)] at h1
  have hs0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hss : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
  have hcs : 1 ≤ c * Real.sqrt m := by
    have h2 : 1 ≤ (c * Real.sqrt m) ^ 2 := by
      rw [mul_pow, sq (Real.sqrt m), hss]; linarith
    nlinarith [mul_nonneg hc.le hs0]
  have hlog : Real.log m ≤ 2 * Real.sqrt m := by
    have h2 : Real.log (Real.sqrt m) = Real.log m / 2 := Real.log_sqrt hm0.le
    have h3 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hm0)
    linarith
  have hsm : Real.sqrt m ≤ c * m := by
    have hcm : c * m = (c * Real.sqrt m) * Real.sqrt m := by rw [mul_assoc, hss]
    rw [hcm]; nlinarith
  have : Real.log m ≤ 3 * c * m := by nlinarith
  rw [show 3 * (c * ((m : ℝ) / Real.log m)) = 3 * c * m / Real.log m by ring,
    le_div_iff₀ hΛ]
  linarith

theorem analytic {C₆ M c α R : ℝ} {a m : ℕ} (hM : 0 < M)
    (hc : c = 1 / (6 * Real.exp 1 * (C₆ + a + 8 + |Real.log M|))) (hC₆ : 0 < C₆)
    (hm : 3 ≤ m) (hαdef : α = 3 * (c * ((m : ℝ) / Real.log m))) (hα : 1 ≤ α)
    (h64 : (m : ℝ) ^ (-C₆) * (1 + Real.exp (-(α * Real.binEntropy (1 / α)))) ^ m ≤ R)
    (hR : R < 32 * Real.exp 1 ∨ R ≤ M * (m : ℝ) ^ (a + 2)) : False := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have he := Real.exp_one_lt_d9
  have he' := Real.exp_one_gt_d9
  have hΛ : 1 ≤ Real.log m := by
    rw [Real.le_log_iff_exp_le hm0]; linarith
  obtain ⟨hb1, hb2⟩ := b_bounds hα
  have hb0 : 0 ≤ Real.exp (-(α * Real.binEntropy (1 / α))) := (Real.exp_pos _).le
  have hlog1b := half_le_log_one_add hb0 hb2
  have hDpos : 0 < C₆ + a + 8 + |Real.log M| := by positivity
  have hα0 : 0 < α := by linarith
  have hmα : (m : ℝ) * (1 / (Real.exp 1 * α)) =
      2 * (C₆ + a + 8 + |Real.log M|) * Real.log m := by
    rw [hαdef, hc]
    field_simp
    ring
  have hmb : (C₆ + a + 8 + |Real.log M|) * Real.log m ≤
      m * Real.log (1 + Real.exp (-(α * Real.binEntropy (1 / α)))) := by
    have h1 := mul_le_mul_of_nonneg_left hb1 hm0.le
    have h3 := mul_le_mul_of_nonneg_left hlog1b hm0.le
    nlinarith
  have hpos : 0 < (m : ℝ) ^ (-C₆) * (1 + Real.exp (-(α * Real.binEntropy (1 / α)))) ^ m := by
    positivity
  have hRpos : 0 < R := lt_of_lt_of_le hpos h64
  have hlogR : -C₆ * Real.log m +
      m * Real.log (1 + Real.exp (-(α * Real.binEntropy (1 / α)))) ≤ Real.log R := by
    have := Real.log_le_log hpos h64
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_rpow hm0, Real.log_pow] at this
  have habs := abs_nonneg (Real.log M)
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hL1 : |Real.log M| ≤ |Real.log M| * Real.log m := by nlinarith
  have ha1 : (a : ℝ) ≤ a * Real.log m := by nlinarith
  rcases hR with h | h
  · have h5 : Real.log R < 5 := by
      rw [Real.log_lt_iff_lt_exp hRpos]
      have hexp : Real.exp 5 = Real.exp 1 ^ 4 * Real.exp 1 := by
        rw [← pow_succ, ← Real.exp_nat_mul]; norm_num
      have h27 : (2.7 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 :=
        pow_le_pow_left₀ (by norm_num) (by linarith) 4
      have h32 : (32 : ℝ) < Real.exp 1 ^ 4 := lt_of_lt_of_le (by norm_num) h27
      rw [hexp]
      nlinarith [mul_lt_mul_of_pos_right h32 (Real.exp_pos 1)]
    nlinarith
  · have h2 : Real.log R ≤ Real.log M + (a + 2) * Real.log m := by
      have := Real.log_le_log hRpos h
      rw [Real.log_mul hM.ne' (by positivity), Real.log_pow] at this
      push_cast at this
      linarith
    have := le_abs_self (Real.log M)
    nlinarith

end RandOnlineSetCoverSqrt.Dev.T15

namespace RandOnlineSetCoverSqrt.LowerBound.Supplement
open RandOnlineSetCoverSqrt.Dev.T15 in
theorem chk_theorem_1_5 :
    ∀ a : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ S : ℕ, S ≤ m ^ a →
      ∀ A : MemAlg m S, A.IsValid →
      ∃ B : List (Element m), B ≠ [] ∧
        c * ((m : ℝ) / Real.log (m : ℝ)) * (listOptNat B : ℝ) ≤ A.expectedCost B := by
  intro a
  obtain ⟨C₆, hC₆, h64⟩ := lemma_6_4
  obtain ⟨c₄, hc₄, h34⟩ := lemma_3_4
  obtain ⟨c₀, hc₀, hG⟩ := Gronemeier.oneWay_disjointness_lower_bound
  set M : ℝ := 3 / (c₀ * c₄) with hM
  have hMpos : 0 < M := by positivity
  set c : ℝ := 1 / (6 * Real.exp 1 * (C₆ + a + 8 + |Real.log M|)) with hc
  have hcpos : 0 < c := by positivity
  refine ⟨c, hcpos, ⌈1 / c ^ 2⌉₊ + 3, ?_⟩
  intro m hm S hS A hA
  by_contra hcon
  push_neg at hcon
  have hm3 : 3 ≤ m := by omega
  have hα := alpha_ge_one hcpos (m := m) (by omega) hm3
  set ρ := c * ((m : ℝ) / Real.log m) with hρ
  have hρ0 : 0 ≤ ρ := by linarith
  set α := 3 * ρ with hαdef
  obtain ⟨h6l, -⟩ := h64 m (by omega) α hα
  have hR : Rm m α < 32 * Real.exp 1 ∨ Rm m α ≤ M * (m : ℝ) ^ (a + 2) := by
    by_cases hbig : Rm m α < 32 * Real.exp 1
    · exact Or.inl hbig
    right
    push_neg at hbig
    have hne : (Finset.range (⌊(m : ℝ) / α⌋₊ + 1)).Nonempty :=
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' hne
      (fun k => (Nat.choose m k : ℝ) / (Nat.choose ⌊α * (k : ℝ)⌋₊ k : ℝ))
    have hRk : Rm m α = (Nat.choose m k : ℝ) / (Nat.choose ⌊α * (k : ℝ)⌋₊ k : ℝ) := hkeq
    rw [hRk] at hbig ⊢
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        simp at hbig
        have := Real.exp_one_gt_d9
        linarith
      · exact h
    have hα1 : (1 : ℝ) ≤ α := hα
    have hkr : k ≤ ⌊α * (k : ℝ)⌋₊ := by
      apply Nat.le_floor
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    have hrm : ⌊α * (k : ℝ)⌋₊ ≤ m := by
      apply Nat.floor_le_of_le
      have hk' : k ≤ ⌊(m : ℝ) / α⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have : (k : ℝ) ≤ m / α :=
        le_trans (by exact_mod_cast hk') (Nat.floor_le (by positivity))
      rw [le_div_iff₀ (by linarith)] at this
      linarith
    obtain ⟨N, hN1, C, hcard, hUE, hineq⟩ := h34 m k _ hk1 hkr hrm hbig
    have hkr3 : 3 * ρ * (k : ℝ) < (⌊α * (k : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hP := protocol_lb A c₀ hG hA ρ hρ0 hcon hUE hcard hkr3
    set q := min m (Nat.choose ⌊α * (k : ℝ)⌋₊ k + 1) with hq
    have hq2 : 2 ≤ q := hUE.2.2.2.1
    have hq0 : (0 : ℝ) < (q : ℝ) ^ 2 := by
      have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
      positivity
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have h1 : (N : ℝ) / (q : ℝ) ^ 2 ≤ ((S : ℝ) + m + 1) / c₀ := by
      rw [div_le_div_iff₀ hq0 hc₀]
      nlinarith
    have h2 := hineq.trans h1
    have hnat : S + m + 1 ≤ 3 * m ^ (a + 1) := by
      have h1 : m ^ a ≤ m ^ (a + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : m ≤ m ^ (a + 1) := Nat.le_self_pow (by omega) m
      have h3 : 1 ≤ m ^ (a + 1) := Nat.one_le_pow _ _ (by omega)
      omega
    have h3 : (S : ℝ) + m + 1 ≤ 3 * (m : ℝ) ^ (a + 1) := by exact_mod_cast hnat
    set R := (Nat.choose m k : ℝ) / (Nat.choose ⌊α * (k : ℝ)⌋₊ k : ℝ) with hRdef
    have h4 : c₄ * R ≤ m * (((S : ℝ) + m + 1) / c₀) := by
      calc c₄ * R = m * (c₄ * (1 / (m : ℝ) * R)) := by field_simp
        _ ≤ m * (((S : ℝ) + m + 1) / c₀) := by gcongr
    rw [hM, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    calc R * (c₀ * c₄) = c₀ * (c₄ * R) := by ring
      _ ≤ c₀ * (m * (((S : ℝ) + m + 1) / c₀)) := by gcongr
      _ = m * ((S : ℝ) + m + 1) := by field_simp
      _ ≤ m * (3 * (m : ℝ) ^ (a + 1)) := by gcongr
      _ = 3 * (m : ℝ) ^ (a + 2) := by ring
  exact analytic hMpos hc hC₆ hm3 rfl hα h6l hR

end RandOnlineSetCoverSqrt.LowerBound.Supplement
end

theorem solution : type_of% @RandOnlineSetCoverSqrt.LowerBound.Supplement.chk_theorem_1_5 := @RandOnlineSetCoverSqrt.LowerBound.Supplement.chk_theorem_1_5
