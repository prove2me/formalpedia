-- Prove2me | solution 1 for ScenarioApproach.Generalization.violation_tail_le_binomial_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T02:24:26.37055+00:00
-- url     : https://prove2.me/submissions/84c50152-e0c4-4116-acc3-7e9118592221

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_ScenarioApproach_Generalization_scenarioProgram

/-! Route F core for 3f312ca3: D1 padding, D2 Helly basis, D4 perturbed program. -/

set_option autoImplicit false

namespace P3f312ca3


section Pad

variable {α X : Type*} [DecidableEq α] (sol : Finset α → X) (feas : X → α → Prop)

/-- `B` is a basis of `S`: a subset with the same solution, minimal for inclusion. -/
def IsBasisOf (S B : Finset α) : Prop :=
  B ⊆ S ∧ sol B = sol S ∧ ∀ B' ⊆ B, sol B' = sol S → B' = B

theorem exists_basisOf (S : Finset α) : ∃ B, IsBasisOf sol S B := by
  classical
  obtain ⟨B, hB, hmin⟩ := Finset.exists_min_image
    (S.powerset.filter fun B => sol B = sol S) Finset.card ⟨S, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hB hmin
  refine ⟨B, hB.1, hB.2, fun B' hB' hsol => ?_⟩
  exact Finset.eq_of_subset_of_card_le hB' (hmin B' ⟨hB'.trans hB.1, hsol⟩)

variable {sol feas}

/-- LP-type axioms for a "unique solution" structure. -/
structure LPType (sol : Finset α → X) (feas : X → α → Prop) : Prop where
  feas_self : ∀ S, ∀ z ∈ S, feas (sol S) z
  ext_feas : ∀ S T, S ⊆ T → (∀ z ∈ T, feas (sol S) z) → sol T = sol S

theorem LPType.sandwich (h : LPType sol feas) {S T U : Finset α} (hST : S ⊆ T) (hTU : T ⊆ U)
    (hSU : sol S = sol U) : sol T = sol S :=
  h.ext_feas S T hST fun z hz => by rw [hSU]; exact h.feas_self U z (hTU hz)

theorem LPType.basisOf_mono (h : LPType sol feas) {S T B : Finset α}
    (hB : IsBasisOf sol S B) (hBT : B ⊆ T) (hTS : T ⊆ S) : IsBasisOf sol T B := by
  have hT : sol T = sol B := h.sandwich hBT hTS hB.2.1
  refine ⟨hBT, hT.symm, fun B' hB' hsol => hB.2.2 B' hB' ?_⟩
  rw [hsol, hT, hB.2.1]

theorem LPType.basisOf_ext (h : LPType sol feas) {I Z B : Finset α}
    (hB : IsBasisOf sol I B) (hIZ : I ⊆ Z) (hf : ∀ z ∈ Z, feas (sol I) z) :
    IsBasisOf sol Z B := by
  have hZ : sol Z = sol I := h.ext_feas I Z hIZ hf
  refine ⟨hB.1.trans hIZ, by rw [hZ, hB.2.1], fun B' hB' hsol => hB.2.2 B' hB' ?_⟩
  rw [hsol, hZ]

/-- The padded `d`-set of `S`: its basis plus the elements of largest label. -/
def IsPad (d : ℕ) (ℓ : α → ℝ) (S I : Finset α) : Prop :=
  ∃ B, IsBasisOf sol S B ∧ B ⊆ I ∧ I ⊆ S ∧ I.card = d ∧ ∀ w ∈ I \ B, ∀ r ∈ S \ I, ℓ r < ℓ w

/-- `z` does not conflict with the padded set `I`. -/
def Good (ℓ : α → ℝ) (I : Finset α) (z : α) : Prop :=
  feas (sol I) z ∧ ∀ B, IsBasisOf sol I B → ∀ w ∈ I \ B, ℓ z < ℓ w

/-- Nondegeneracy on a universe `U`: every subset has a unique basis. -/
def Nondeg (sol : Finset α → X) (U : Finset α) : Prop :=
  ∀ S ⊆ U, ∀ B₁ B₂, IsBasisOf sol S B₁ → IsBasisOf sol S B₂ → B₁ = B₂

/-- D1 (hereditary padding): `I` is the padded set of `S` iff it has `d` elements and no
element of `S \ I` conflicts with it. -/
theorem LPType.isPad_iff (h : LPType sol feas) {U : Finset α} (hnd : Nondeg sol U)
    {d : ℕ} (ℓ : α → ℝ) {S I : Finset α} (hSU : S ⊆ U) (hIS : I ⊆ S) :
    IsPad (sol := sol) d ℓ S I ↔ I.card = d ∧ ∀ z ∈ S \ I, Good (sol := sol) (feas := feas) ℓ I z := by
  constructor
  · rintro ⟨B, hB, hBI, -, hcard, hlab⟩
    have hBI' : IsBasisOf sol I B := h.basisOf_mono hB hBI hIS
    have hsol : sol I = sol S := (h.sandwich hBI hIS hB.2.1).trans hB.2.1
    refine ⟨hcard, fun z hz => ⟨?_, fun B₂ hB₂ w hw => ?_⟩⟩
    · rw [hsol]; exact h.feas_self S z (Finset.mem_sdiff.1 hz).1
    · have : B₂ = B := hnd I (hIS.trans hSU) B₂ B hB₂ hBI'
      subst this
      exact hlab w hw z hz
  · rintro ⟨hcard, hgood⟩
    obtain ⟨B, hB⟩ := exists_basisOf sol I
    have hf : ∀ z ∈ S, feas (sol I) z := by
      intro z hz
      by_cases hzI : z ∈ I
      · exact h.feas_self I z hzI
      · exact (hgood z (Finset.mem_sdiff.2 ⟨hz, hzI⟩)).1
    refine ⟨B, h.basisOf_ext hB hIS hf, hB.1, hIS, hcard, fun w hw r hr => ?_⟩
    exact (hgood r hr).2 B hB w hw

/-- Top-`k` elements of a finset by an injective label. -/
theorem exists_top (ℓ : α → ℝ) : ∀ (k : ℕ) (R : Finset α), Set.InjOn ℓ R → k ≤ R.card →
    ∃ P ⊆ R, P.card = k ∧ ∀ p ∈ P, ∀ r ∈ R \ P, ℓ r < ℓ p := by
  intro k
  induction k with
  | zero => intro R _ _; exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  | succ k ih =>
    intro R hinj hk
    have hne : R.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image R ℓ hne
    have hcard : k ≤ (R.erase m).card := by rw [Finset.card_erase_of_mem hm]; omega
    obtain ⟨P, hPR, hPc, hP⟩ := ih (R.erase m) (hinj.mono (by simp)) hcard
    have hmP : m ∉ P := fun h => by simpa using hPR h
    refine ⟨insert m P, Finset.insert_subset hm (hPR.trans (Finset.erase_subset _ _)), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hmP, hPc]
    · intro p hp r hr
      rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at hr
      rcases Finset.mem_insert.1 hp with rfl | hp
      · refine lt_of_le_of_ne (hmax r hr.1) fun heq => hr.2.1 ?_
        exact hinj hr.1 hm heq
      · exact hP p hp r (Finset.mem_sdiff.2 ⟨Finset.mem_erase.2 ⟨hr.2.1, hr.1⟩, hr.2.2⟩)

/-- Existence of the padded set. -/
theorem exists_isPad {d : ℕ} (ℓ : α → ℝ) {S : Finset α} (hinj : Set.InjOn ℓ S)
    (hdS : d ≤ S.card) (hbd : ∀ B, IsBasisOf sol S B → B.card ≤ d) :
    ∃ I, IsPad (sol := sol) d ℓ S I := by
  obtain ⟨B, hB⟩ := exists_basisOf sol S
  have hBd := hbd B hB
  have hk : d - B.card ≤ (S \ B).card := by
    rw [Finset.card_sdiff_of_subset hB.1]; omega
  obtain ⟨P, hPS, hPc, hP⟩ := exists_top ℓ (d - B.card) (S \ B) (hinj.mono (by simp)) hk
  have hdisj : Disjoint B P := by
    rw [Finset.disjoint_left]; intro x hxB hxP; exact (Finset.mem_sdiff.1 (hPS hxP)).2 hxB
  refine ⟨B ∪ P, B, hB, Finset.subset_union_left, Finset.union_subset hB.1
    (hPS.trans Finset.sdiff_subset), ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hPc]; omega
  · intro w hw r hr
    have hwP : w ∈ P := by
      rw [Finset.mem_sdiff, Finset.mem_union] at hw; tauto
    have hr' : r ∈ (S \ B) \ P := by
      rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hr
      exact Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨hr.1, hr.2.1⟩, hr.2.2⟩
    exact hP w hwP r hr'

/-- Uniqueness of the padded set. -/
theorem isPad_unique {U : Finset α} (hnd : Nondeg sol U) {d : ℕ} (ℓ : α → ℝ) {S I₁ I₂ : Finset α}
    (hSU : S ⊆ U) (h₁ : IsPad (sol := sol) d ℓ S I₁) (h₂ : IsPad (sol := sol) d ℓ S I₂) :
    I₁ = I₂ := by
  obtain ⟨B₁, hB₁, hB₁I, hI₁S, hc₁, hl₁⟩ := h₁
  obtain ⟨B₂, hB₂, hB₂I, hI₂S, hc₂, hl₂⟩ := h₂
  have hB : B₂ = B₁ := hnd S hSU B₂ B₁ hB₂ hB₁
  subst hB
  by_contra hne
  have hsub : ¬ I₁ ⊆ I₂ := fun hs =>
    hne (Finset.eq_of_subset_of_card_le hs (by rw [hc₁, hc₂]))
  obtain ⟨w, hw1, hw2⟩ := Finset.not_subset.1 hsub
  have hsub' : ¬ I₂ ⊆ I₁ := fun hs =>
    hne (Finset.eq_of_subset_of_card_le hs (by rw [hc₁, hc₂])).symm
  obtain ⟨v, hv2, hv1⟩ := Finset.not_subset.1 hsub'
  have hwB : w ∉ B₂ := fun h => hw2 (hB₂I h)
  have hvB : v ∉ B₂ := fun h => hv1 (hB₁I h)
  have h1 := hl₁ w (Finset.mem_sdiff.2 ⟨hw1, hwB⟩) v (Finset.mem_sdiff.2 ⟨hI₂S hv2, hv1⟩)
  have h2 := hl₂ v (Finset.mem_sdiff.2 ⟨hv2, hvB⟩) w (Finset.mem_sdiff.2 ⟨hI₁S hw1, hw2⟩)
  linarith

end Pad



theorem helly_basis {d : ℕ} {ι : Type*} [DecidableEq ι]
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : Convex ℝ K)
    {C : ι → Set (EuclideanSpace ℝ (Fin d))} (hC : ∀ i, Convex ℝ (C i))
    (sol : Finset ι → EuclideanSpace ℝ (Fin d))
    (hmem : ∀ S, sol S ∈ K ∧ ∀ i ∈ S, sol S ∈ C i)
    (hopt : ∀ S y, y ∈ K → (∀ i ∈ S, y ∈ C i) → f (sol S) ≤ f y)
    (huniq : ∀ S y, y ∈ K → (∀ i ∈ S, y ∈ C i) →
      (∀ z, z ∈ K → (∀ i ∈ S, z ∈ C i) → f y ≤ f z) → y = sol S)
    (S : Finset ι) : ∃ J ⊆ S, J.card ≤ d ∧ sol J = sol S := by
  classical
  set v := f (sol S) with hv
  let G : Option ι → Set (EuclideanSpace ℝ (Fin d)) := fun o =>
    match o with
    | none => K ∩ {y | f y < v}
    | some i => C i
  set s : Finset (Option ι) := insert none (S.map Function.Embedding.some) with hs
  have hGc : ∀ o ∈ s, Convex ℝ (G o) := by
    intro o _
    cases o with
    | none =>
      have h1 := hf.convex_lt v
      simp only [Set.mem_univ, true_and] at h1
      exact hK.inter h1
    | some i => exact hC i
  have hempty : ¬ (⋂ o ∈ s, G o).Nonempty := by
    rintro ⟨y, hy⟩
    simp only [Set.mem_iInter] at hy
    have h0 : y ∈ K ∩ {y | f y < v} := hy none (by simp [hs])
    have hyC : ∀ i ∈ S, y ∈ C i := fun i hi => hy (some i) (by simp [hs, hi])
    exact absurd (hopt S y h0.1 hyC) (not_le.2 h0.2)
  have hex : ∃ I ⊆ s, I.card ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) + 1 ∧
      ¬ (⋂ o ∈ I, G o).Nonempty := by
    by_contra hcon
    push_neg at hcon
    exact hempty (Convex.helly_theorem' hGc hcon)
  obtain ⟨I, hIs, hIcard, hIe⟩ := hex
  rw [finrank_euclideanSpace_fin] at hIcard
  have hnone : none ∈ I := by
    by_contra hn
    apply hIe
    refine ⟨sol S, ?_⟩
    simp only [Set.mem_iInter]
    intro o ho
    cases o with
    | none => exact absurd ho hn
    | some i =>
      have : some i ∈ s := hIs ho
      simp only [hs, Finset.mem_insert, Finset.mem_map, Function.Embedding.some_apply,
        reduceCtorEq, false_or, Option.some.injEq, exists_eq_right] at this
      exact (hmem S).2 i this
  set J := S.filter (fun i => some i ∈ I) with hJ
  have hJS : J ⊆ S := Finset.filter_subset _ _
  have hJcard : J.card ≤ d := by
    have hsub : J.map Function.Embedding.some ⊆ I.erase none := by
      intro o ho
      simp only [Finset.mem_map, hJ, Finset.mem_filter, Function.Embedding.some_apply] at ho
      obtain ⟨i, ⟨_, hi⟩, rfl⟩ := ho
      exact Finset.mem_erase.2 ⟨by simp, hi⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_map, Finset.card_erase_of_mem hnone] at this
    omega
  have hoptJ : ∀ z, z ∈ K → (∀ i ∈ J, z ∈ C i) → f (sol S) ≤ f z := by
    intro z hzK hzC
    by_contra hlt
    push_neg at hlt
    apply hIe
    refine ⟨z, ?_⟩
    simp only [Set.mem_iInter]
    intro o ho
    cases o with
    | none => exact ⟨hzK, hlt⟩
    | some i =>
      have : some i ∈ s := hIs ho
      simp only [hs, Finset.mem_insert, Finset.mem_map, Function.Embedding.some_apply,
        reduceCtorEq, false_or, Option.some.injEq, exists_eq_right] at this
      exact hzC i (by simp [hJ, this, ho])
  refine ⟨J, hJS, hJcard, ?_⟩
  exact (huniq J (sol S) (hmem S).1 (fun i hi => (hmem S).2 i (hJS hi)) hoptJ).symm



section Thick

variable {d : ℕ}

/-- The perturbed objective. -/
noncomputable def fobj (c : EuclideanSpace ℝ (Fin d)) (ε : ℝ) (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ c θ + ε * ‖θ‖ ^ 2

theorem fobj_continuous (c : EuclideanSpace ℝ (Fin d)) (ε : ℝ) : Continuous (fobj c ε) := by
  unfold fobj; fun_prop

theorem norm_sq_comb (x y : EuclideanSpace ℝ (Fin d)) (a b : ℝ) (hab : a + b = 1) :
    ‖a • x + b • y‖ ^ 2 = a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 - a * b * ‖x - y‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, inner_sub_left, inner_sub_right, real_inner_comm x y, RCLike.conj_to_real]
  linear_combination (a * inner ℝ x x + b * inner ℝ y y) * hab

theorem fobj_comb (c : EuclideanSpace ℝ (Fin d)) (ε : ℝ) (x y : EuclideanSpace ℝ (Fin d))
    (a b : ℝ) (hab : a + b = 1) :
    fobj c ε (a • x + b • y) = a * fobj c ε x + b * fobj c ε y - ε * (a * b) * ‖x - y‖ ^ 2 := by
  unfold fobj
  rw [norm_sq_comb x y a b hab, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  ring

theorem fobj_convex (c : EuclideanSpace ℝ (Fin d)) {ε : ℝ} (hε : 0 ≤ ε) :
    ConvexOn ℝ Set.univ (fobj c ε) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  rw [smul_eq_mul, smul_eq_mul, fobj_comb c ε x y a b hab]
  have : 0 ≤ ε * (a * b) * ‖x - y‖ ^ 2 := by positivity
  linarith

theorem exists_min_fobj (c : EuclideanSpace ℝ (Fin d)) {ε : ℝ} (hε : 0 < ε)
    {F : Set (EuclideanSpace ℝ (Fin d))} (hF : IsClosed F) (hne : F.Nonempty) :
    ∃ x ∈ F, ∀ y ∈ F, fobj c ε x ≤ fobj c ε y := by
  obtain ⟨θ0, h0⟩ := hne
  set R := ‖θ0‖ + (‖c‖ + |fobj c ε θ0|) / ε + 1 with hR
  have hR1 : 1 ≤ R := by
    have : 0 ≤ (‖c‖ + |fobj c ε θ0|) / ε := by positivity
    have : 0 ≤ ‖θ0‖ := norm_nonneg _
    linarith
  have hK : IsCompact (F ∩ Metric.closedBall 0 R) := (isCompact_closedBall 0 R).inter_left hF
  have h0R : θ0 ∈ F ∩ Metric.closedBall 0 R := by
    refine ⟨h0, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have : 0 ≤ (‖c‖ + |fobj c ε θ0|) / ε := by positivity
    linarith
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn ⟨θ0, h0R⟩ (fobj_continuous c ε).continuousOn
  refine ⟨x, hx.1, fun y hy => ?_⟩
  by_cases hyR : ‖y‖ ≤ R
  · exact isMinOn_iff.1 hmin y ⟨hy, by rwa [Metric.mem_closedBall, dist_zero_right]⟩
  · push_neg at hyR
    refine (isMinOn_iff.1 hmin θ0 h0R).trans ?_
    have hdiv : (‖c‖ + |fobj c ε θ0|) / ε * ε = ‖c‖ + |fobj c ε θ0| := div_mul_cancel₀ _ hε.ne'
    have ht : ‖c‖ + |fobj c ε θ0| + ε ≤ ε * ‖y‖ := by
      have : (‖c‖ + |fobj c ε θ0|) / ε + 1 ≤ ‖y‖ := by
        have : 0 ≤ ‖θ0‖ := norm_nonneg _
        linarith
      nlinarith
    have hin : -(‖c‖ * ‖y‖) ≤ inner ℝ c y := by
      have := abs_real_inner_le_norm c y
      linarith [neg_abs_le (inner ℝ c y)]
    have hy1 : 1 ≤ ‖y‖ := by linarith
    have hA : fobj c ε θ0 ≤ |fobj c ε θ0| := le_abs_self _
    have h2 : ‖y‖ * (ε * ‖y‖ - ‖c‖) ≤ fobj c ε y := by
      have e : ‖y‖ * (ε * ‖y‖ - ‖c‖) = ε * ‖y‖ ^ 2 - ‖c‖ * ‖y‖ := by ring
      rw [e]; unfold fobj; linarith
    have h3 : 1 * (|fobj c ε θ0| + ε) ≤ ‖y‖ * (ε * ‖y‖ - ‖c‖) :=
      mul_le_mul hy1 (by linarith) (by positivity) (norm_nonneg _)
    linarith

theorem fobj_unique (c : EuclideanSpace ℝ (Fin d)) {ε : ℝ} (hε : 0 < ε)
    {F : Set (EuclideanSpace ℝ (Fin d))} (hF : Convex ℝ F) {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ F) (hy : y ∈ F) (hxm : ∀ z ∈ F, fobj c ε x ≤ fobj c ε z)
    (hym : ∀ z ∈ F, fobj c ε y ≤ fobj c ε z) : x = y := by
  have hm : (1/2 : ℝ) • x + (1/2 : ℝ) • y ∈ F := hF hx hy (by norm_num) (by norm_num) (by norm_num)
  have h1 := hxm _ hm
  have h2 := hym _ hm
  rw [fobj_comb c ε x y (1/2) (1/2) (by norm_num)] at h1 h2
  have h3 : ‖x - y‖ ^ 2 ≤ 0 := by nlinarith
  have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- Tightness: an element of a minimal basis is not interior-satisfied at the solution. -/
theorem not_mem_interior_of_minimal {ι : Type*} [DecidableEq ι]
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : Convex ℝ K)
    {C : ι → Set (EuclideanSpace ℝ (Fin d))} (hC : ∀ i, Convex ℝ (C i))
    (sol : Finset ι → EuclideanSpace ℝ (Fin d))
    (hmem : ∀ S, sol S ∈ K ∧ ∀ i ∈ S, sol S ∈ C i)
    (hopt : ∀ S y, y ∈ K → (∀ i ∈ S, y ∈ C i) → f (sol S) ≤ f y)
    (huniq : ∀ S y, y ∈ K → (∀ i ∈ S, y ∈ C i) →
      (∀ z, z ∈ K → (∀ i ∈ S, z ∈ C i) → f y ≤ f z) → y = sol S)
    {T : Finset ι} (hmin : ∀ B' ⊆ T, sol B' = sol T → B' = T) {z : ι} (hz : z ∈ T) :
    sol T ∉ interior (C z) := by
  intro hint
  set x := sol T with hxdef
  have hopt' : ∀ y, y ∈ K → (∀ i ∈ T.erase z, y ∈ C i) → f x ≤ f y := by
    intro y hyK hyC
    by_contra hlt
    push_neg at hlt
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
    by_cases hD : ‖y - x‖ = 0
    · have : y = x := sub_eq_zero.1 (norm_eq_zero.1 hD)
      rw [this] at hlt; exact lt_irrefl _ hlt
    have hDpos : 0 < ‖y - x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hD)
    set t := min 1 (δ / (2 * ‖y - x‖)) with ht
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htD : t * ‖y - x‖ < δ := by
      have : t ≤ δ / (2 * ‖y - x‖) := min_le_right _ _
      calc t * ‖y - x‖ ≤ δ / (2 * ‖y - x‖) * ‖y - x‖ := by gcongr
        _ = δ / 2 := by field_simp
        _ < δ := by linarith
    set p := x + t • (y - x) with hp
    have hpK : p ∈ K := hK.add_smul_sub_mem (hmem T).1 hyK ⟨ht0.le, ht1⟩
    have hpC : ∀ i ∈ T, p ∈ C i := by
      intro i hi
      by_cases hiz : i = z
      · subst hiz
        apply hball
        rw [Metric.mem_ball, hp, dist_self_add_left, norm_smul, Real.norm_of_nonneg ht0.le]
        exact htD
      · exact (hC i).add_smul_sub_mem ((hmem T).2 i hi) (hyC i (Finset.mem_erase.2 ⟨hiz, hi⟩))
          ⟨ht0.le, ht1⟩
    have hle := hopt T p hpK hpC
    have hconv : f p ≤ (1 - t) * f x + t * f y := by
      have := hf.2 (Set.mem_univ x) (Set.mem_univ y) (by linarith : (0:ℝ) ≤ 1 - t) ht0.le
        (by ring : (1 - t) + t = 1)
      have heq : (1 - t) • x + t • y = p := by
        rw [hp, smul_sub, sub_smul, one_smul]; abel
      rw [heq, smul_eq_mul, smul_eq_mul] at this
      exact this
    nlinarith
  have hx' : x = sol (T.erase z) := huniq (T.erase z) x (hmem T).1
    (fun i hi => (hmem T).2 i (Finset.mem_of_mem_erase hi)) hopt'
  have h4 := hmin (T.erase z) (Finset.erase_subset _ _) hx'.symm
  have h5 : z ∈ T.erase z := by rw [h4]; exact hz
  exact (Finset.notMem_erase z T) h5

/-- Nondegeneracy from the absence of ties. -/
theorem basis_unique_of_noTie {ι : Type*} [DecidableEq ι]
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : Convex ℝ K)
    {C : ι → Set (EuclideanSpace ℝ (Fin d))} (hC : ∀ i, Convex ℝ (C i))
    (sol : Finset ι → EuclideanSpace ℝ (Fin d))
    (hmem : ∀ S, sol S ∈ K ∧ ∀ i ∈ S, sol S ∈ C i)
    (hopt : ∀ S y, y ∈ K → (∀ i ∈ S, y ∈ C i) → f (sol S) ≤ f y)
    (huniq : ∀ S y, y ∈ K → (∀ i ∈ S, y ∈ C i) →
      (∀ z, z ∈ K → (∀ i ∈ S, z ∈ C i) → f y ≤ f z) → y = sol S)
    (U : Finset ι)
    (hnt : ∀ B ⊆ U, ∀ z ∈ U, z ∉ B → sol B ∈ C z → sol B ∈ interior (C z)) :
    ∀ S ⊆ U, ∀ B₁ B₂, IsBasisOf sol S B₁ → IsBasisOf sol S B₂ → B₁ = B₂ := by
  intro S hSU B₁ B₂ h₁ h₂
  by_contra hne
  have hsub : ¬ B₂ ⊆ B₁ := fun h => hne (h₁.2.2 B₂ h h₂.2.1).symm
  obtain ⟨z, hz2, hz1⟩ := Finset.not_subset.1 hsub
  have hsol : sol B₁ = sol B₂ := h₁.2.1.trans h₂.2.1.symm
  have hzC : sol B₁ ∈ C z := by rw [h₁.2.1]; exact (hmem S).2 z (h₂.1 hz2)
  have hint := hnt B₁ (h₁.1.trans hSU) z (hSU (h₂.1 hz2)) hz1 hzC
  rw [hsol] at hint
  have hmin₂ : ∀ B' ⊆ B₂, sol B' = sol B₂ → B' = B₂ := fun B' hB' h =>
    h₂.2.2 B' hB' (h.trans h₂.2.1)
  exact not_mem_interior_of_minimal hf hK hC sol hmem hopt huniq hmin₂ hz2 hint

/-- D4m: the minimiser of the perturbed objective over a measurable family of closed convex sets
with nonempty interior is measurable (countable dense characterisation). -/
theorem argmin_measurable {Ω : Type*} [MeasurableSpace Ω] (c : EuclideanSpace ℝ (Fin d)) {ε : ℝ}
    (hε : 0 < ε) (F : Ω → Set (EuclideanSpace ℝ (Fin d)))
    (hFm : ∀ q, MeasurableSet {ω | q ∈ F ω})
    (hFc : ∀ ω, IsClosed (F ω)) (hFv : ∀ ω, Convex ℝ (F ω))
    (hFi : ∀ ω, (interior (F ω)).Nonempty)
    (s : Ω → EuclideanSpace ℝ (Fin d))
    (hs : ∀ ω, s ω ∈ F ω ∧ ∀ y ∈ F ω, fobj c ε (s ω) ≤ fobj c ε y) :
    Measurable s := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (EuclideanSpace ℝ (Fin d))
  have : Countable D := hDc.to_subtype
  set f := fobj c ε with hf
  have hfc : Continuous f := fobj_continuous c ε
  -- approximation of the minimum by dense points inside an open set
  have happrox : ∀ ω (U : Set (EuclideanSpace ℝ (Fin d))), IsOpen U → s ω ∈ U → ∀ η > 0,
      ∃ q ∈ D, (q ∈ F ω ∧ q ∈ U) ∧ f q < f (s ω) + η := by
    intro ω U hU hsU η hη
    have hcl : s ω ∈ closure (interior (F ω)) := by
      rw [(hFv ω).closure_interior_eq_closure_of_nonempty_interior (hFi ω), (hFc ω).closure_eq]
      exact (hs ω).1
    have hnb : {y | f y < f (s ω) + η} ∈ nhds (s ω) :=
      hfc.continuousAt.eventually (gt_mem_nhds (by linarith))
    obtain ⟨O, hOsub, hOopen, hsO⟩ := mem_nhds_iff.1 (Filter.inter_mem (hU.mem_nhds hsU) hnb)
    have hne : (O ∩ interior (F ω)).Nonempty := mem_closure_iff.1 hcl O hOopen hsO
    obtain ⟨q, hq1, hq2⟩ := hDd.inter_open_nonempty (O ∩ interior (F ω))
      (hOopen.inter isOpen_interior) hne
    exact ⟨q, hq2, ⟨interior_subset hq1.2, (hOsub hq1.1).1⟩, (hOsub hq1.1).2⟩
  -- the measurable characterisation of `{ω | s ω j ≤ a}`
  have hchar : ∀ (j : Fin d) (a : ℝ) (ω : Ω), EuclideanSpace.proj j (s ω) ≤ a ↔
      ∀ n : ℕ, ∀ p : D, (p : EuclideanSpace ℝ (Fin d)) ∈ F ω → ∃ q : D,
        (q : EuclideanSpace ℝ (Fin d)) ∈ F ω ∧
        EuclideanSpace.proj j (q : EuclideanSpace ℝ (Fin d)) < a + 1 / ((n : ℝ) + 1) ∧
        f q < f p + 1 / ((n : ℝ) + 1) := by
    intro j a ω
    have hpc : Continuous (fun θ : EuclideanSpace ℝ (Fin d) => EuclideanSpace.proj j θ) :=
      (EuclideanSpace.proj j).continuous
    constructor
    · intro hle n p hp
      have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨q, hqD, ⟨hqF, hqU⟩, hqf⟩ := happrox ω
        {θ | EuclideanSpace.proj j θ < a + 1 / ((n : ℝ) + 1)}
        (isOpen_lt hpc continuous_const) (by simp only [Set.mem_setOf_eq]; linarith)
        (1 / ((n : ℝ) + 1)) hpos
      refine ⟨⟨q, hqD⟩, hqF, hqU, ?_⟩
      have := (hs ω).2 p hp
      simp only at this ⊢
      linarith
    · intro H
      by_contra hgt
      push_neg at hgt
      -- choose n0 with a + 1/(n0+1) < s_j
      obtain ⟨n0, hn0⟩ := exists_nat_one_div_lt (sub_pos.2 hgt)
      set G := F ω ∩ {θ | EuclideanSpace.proj j θ ≤ a + 1 / ((n0 : ℝ) + 1)} with hG
      have hGc : IsClosed G := (hFc ω).inter (isClosed_le hpc continuous_const)
      -- a dense point of F ω exists
      obtain ⟨p0, hp0D, ⟨hp0F, -⟩, -⟩ := happrox ω Set.univ isOpen_univ (Set.mem_univ _) 1 one_pos
      by_cases hGne : G.Nonempty
      · obtain ⟨y, hyG, hymin⟩ := exists_min_fobj c hε hGc hGne
        have hys : f (s ω) < f y := by
          rcases lt_or_eq_of_le ((hs ω).2 y hyG.1) with h | h
          · exact h
          · exfalso
            have hyopt : ∀ z ∈ F ω, f y ≤ f z := fun z hz => h ▸ (hs ω).2 z hz
            have := fobj_unique c hε (hFv ω) (hs ω).1 hyG.1 (hs ω).2 hyopt
            have h1 : EuclideanSpace.proj j y ≤ a + 1 / ((n0 : ℝ) + 1) := hyG.2
            rw [← this] at h1
            linarith
        set g := f y - f (s ω) with hgdef
        have hg : 0 < g := by linarith
        obtain ⟨n1, hn1⟩ := exists_nat_one_div_lt (half_pos hg)
        obtain ⟨p, hpD, ⟨hpF, -⟩, hpf⟩ := happrox ω Set.univ isOpen_univ (Set.mem_univ _)
          (g / 2) (half_pos hg)
        obtain ⟨q, hqF, hqj, hqf⟩ := H (max n0 n1) ⟨p, hpD⟩ hpF
        have hmn : 1 / ((max n0 n1 : ℕ) + 1 : ℝ) ≤ 1 / ((n0 : ℝ) + 1) := by
          gcongr; exact_mod_cast le_max_left n0 n1
        have hmn' : 1 / ((max n0 n1 : ℕ) + 1 : ℝ) ≤ 1 / ((n1 : ℝ) + 1) := by
          gcongr; exact_mod_cast le_max_right n0 n1
        have hqG : (q : EuclideanSpace ℝ (Fin d)) ∈ G := ⟨hqF, by
          simp only [Set.mem_setOf_eq]; linarith⟩
        have := hymin q hqG
        simp only at hqf
        linarith
      · obtain ⟨q, hqF, hqj, -⟩ := H n0 ⟨p0, hp0D⟩ hp0F
        exact hGne ⟨q, hqF, le_of_lt hqj⟩
  -- measurability of the coordinates
  have hcoord : ∀ j : Fin d, Measurable (fun ω => EuclideanSpace.proj j (s ω)) := by
    intro j
    refine measurable_of_Iic fun a => ?_
    have : (fun ω => EuclideanSpace.proj j (s ω)) ⁻¹' Set.Iic a =
        ⋂ n : ℕ, ⋂ p : D, ({ω | (p : EuclideanSpace ℝ (Fin d)) ∈ F ω}ᶜ ∪
          ⋃ q : D, ({ω | (q : EuclideanSpace ℝ (Fin d)) ∈ F ω} ∩
            {_ω | EuclideanSpace.proj j (q : EuclideanSpace ℝ (Fin d)) < a + 1 / ((n : ℝ) + 1) ∧
              f q < f p + 1 / ((n : ℝ) + 1)})) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iic, hchar j a ω, Set.mem_iInter, Set.mem_union,
        Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      refine forall_congr' fun n => forall_congr' fun p => ?_
      constructor
      · intro h
        by_cases hp : (p : EuclideanSpace ℝ (Fin d)) ∈ F ω
        · obtain ⟨q, h1, h2, h3⟩ := h hp
          exact Or.inr ⟨q, h1, h2, h3⟩
        · exact Or.inl hp
      · rintro (h | ⟨q, h1, h2, h3⟩) hp
        · exact absurd hp h
        · exact ⟨q, h1, h2, h3⟩
    rw [this]
    exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun p =>
      (hFm p).compl.union (MeasurableSet.iUnion fun q => (hFm q).inter (MeasurableSet.const _))
  have hmeq : Measurable (fun ω => (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm (s ω)) :=
    measurable_pi_iff.2 fun j => hcoord j
  have := (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp hmeq
  convert this using 1
  funext ω
  exact ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).apply_symm_apply (s ω)).symm

end Thick


section Setting

variable {d L : ℕ}

/-- Radius of the heated constraint of the point `z = (k, u)`. -/
noncomputable def rad (ε : ℝ) (z : Fin L × ℝ) : ℝ := ε * (1 + |z.2|)

/-- Heated constraint set. -/
def Cset (Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) (z : Fin L × ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  Metric.cthickening (rad ε z) (Θk z.1)

/-- Heated feasible set of the sub-sample `S`. -/
def Feps (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θk : Fin L → Set (EuclideanSpace ℝ (Fin d)))
    (ε : ℝ) {M : ℕ} (ω : Fin M → Fin L × ℝ) (S : Finset (Fin M)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  Metric.cthickening ε Θ ∩ ⋂ i ∈ S, Cset Θk ε (ω i)

/-- The minimiser of the perturbed objective over a set (junk value if none). -/
noncomputable def solOf (c : EuclideanSpace ℝ (Fin d)) (ε : ℝ) (F : Set (EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin d) := by
  classical
  exact if h : ∃ x ∈ F, ∀ y ∈ F, fobj c ε x ≤ fobj c ε y then Classical.choose h else 0

theorem solOf_spec (c : EuclideanSpace ℝ (Fin d)) {ε : ℝ} (hε : 0 < ε)
    {F : Set (EuclideanSpace ℝ (Fin d))} (hF : IsClosed F) (hne : F.Nonempty) :
    solOf c ε F ∈ F ∧ ∀ y ∈ F, fobj c ε (solOf c ε F) ≤ fobj c ε y := by
  unfold solOf
  split_ifs with h
  · exact (Classical.choose_spec h)
  · exact absurd (exists_min_fobj c hε hF hne) h

theorem rad_ge {ε : ℝ} (hε : 0 ≤ ε) (z : Fin L × ℝ) : ε ≤ rad ε z := by
  unfold rad; nlinarith [abs_nonneg z.2]

theorem isClosed_Feps (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) {M : ℕ} (ω : Fin M → Fin L × ℝ)
    (S : Finset (Fin M)) : IsClosed (Feps Θ Θk ε ω S) :=
  Metric.isClosed_cthickening.inter (isClosed_biInter fun _ _ => Metric.isClosed_cthickening)

theorem convex_Feps {Θ : Set (EuclideanSpace ℝ (Fin d))} (hΘ : Convex ℝ Θ)
    {Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))} (hΘk : ∀ k, Convex ℝ (Θk k)) (ε : ℝ) {M : ℕ}
    (ω : Fin M → Fin L × ℝ) (S : Finset (Fin M)) : Convex ℝ (Feps Θ Θk ε ω S) :=
  (hΘ.cthickening ε).inter (convex_iInter₂ fun i _ => (hΘk (ω i).1).cthickening _)

/-- The heated feasible set contains the `ε`-ball around any original feasible point. -/
theorem ball_subset_Feps {Θ : Set (EuclideanSpace ℝ (Fin d))}
    {Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ} (hε : 0 ≤ ε) {M : ℕ}
    (ω : Fin M → Fin L × ℝ) (S : Finset (Fin M)) {θ0 : EuclideanSpace ℝ (Fin d)}
    (h0 : θ0 ∈ Θ ∩ ⋂ i ∈ S, Θk (ω i).1) :
    Metric.ball θ0 ε ⊆ Feps Θ Θk ε ω S := by
  intro x hx
  have hb : ∀ (A : Set (EuclideanSpace ℝ (Fin d))) (r : ℝ), θ0 ∈ A → ε ≤ r →
      x ∈ Metric.cthickening r A := by
    intro A r hA hr
    exact Metric.cthickening_mono hr A
      (Metric.thickening_subset_cthickening ε A (Metric.ball_subset_thickening hA ε hx))
  refine ⟨hb Θ ε h0.1 le_rfl, ?_⟩
  simp only [Set.mem_iInter]
  intro i hi
  exact hb _ _ (Set.mem_iInter₂.1 h0.2 i hi) (rad_ge hε (ω i))

/-- Specification of the heated solution map of a sample. -/
structure HeatSpec (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) {M : ℕ} (ω : Fin M → Fin L × ℝ) :
    Prop where
  mem : ∀ S, solOf c ε (Feps Θ Θk ε ω S) ∈ Metric.cthickening ε Θ ∧
    ∀ i ∈ S, solOf c ε (Feps Θ Θk ε ω S) ∈ Cset Θk ε (ω i)
  opt : ∀ S y, y ∈ Metric.cthickening ε Θ → (∀ i ∈ S, y ∈ Cset Θk ε (ω i)) →
    fobj c ε (solOf c ε (Feps Θ Θk ε ω S)) ≤ fobj c ε y
  uniq : ∀ S y, y ∈ Metric.cthickening ε Θ → (∀ i ∈ S, y ∈ Cset Θk ε (ω i)) →
    (∀ z, z ∈ Metric.cthickening ε Θ → (∀ i ∈ S, z ∈ Cset Θk ε (ω i)) →
      fobj c ε y ≤ fobj c ε z) → y = solOf c ε (Feps Θ Θk ε ω S)

theorem mem_Feps_iff {Θ : Set (EuclideanSpace ℝ (Fin d))}
    {Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ} {M : ℕ} {ω : Fin M → Fin L × ℝ}
    {S : Finset (Fin M)} {y : EuclideanSpace ℝ (Fin d)} :
    y ∈ Feps Θ Θk ε ω S ↔ y ∈ Metric.cthickening ε Θ ∧ ∀ i ∈ S, y ∈ Cset Θk ε (ω i) := by
  simp [Feps, Set.mem_iInter]

theorem heatSpec (c : EuclideanSpace ℝ (Fin d)) {Θ : Set (EuclideanSpace ℝ (Fin d))}
    (hΘ : Convex ℝ Θ) {Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))} (hΘk : ∀ k, Convex ℝ (Θk k))
    {ε : ℝ} (hε : 0 < ε) {M : ℕ} (ω : Fin M → Fin L × ℝ)
    (hne : ∀ S : Finset (Fin M), (Θ ∩ ⋂ i ∈ S, Θk (ω i).1).Nonempty) :
    HeatSpec c Θ Θk ε ω := by
  have hspec : ∀ S, solOf c ε (Feps Θ Θk ε ω S) ∈ Feps Θ Θk ε ω S ∧
      ∀ y ∈ Feps Θ Θk ε ω S, fobj c ε (solOf c ε (Feps Θ Θk ε ω S)) ≤ fobj c ε y := by
    intro S
    obtain ⟨θ0, h0⟩ := hne S
    exact solOf_spec c hε (isClosed_Feps Θ Θk ε ω S)
      ⟨θ0, ball_subset_Feps hε.le ω S h0 (Metric.mem_ball_self hε)⟩
  refine ⟨fun S => mem_Feps_iff.1 (hspec S).1, fun S y hy1 hy2 => (hspec S).2 y
    (mem_Feps_iff.2 ⟨hy1, hy2⟩), fun S y hy1 hy2 hymin => ?_⟩
  exact fobj_unique c hε (convex_Feps hΘ hΘk ε ω S) (mem_Feps_iff.2 ⟨hy1, hy2⟩) (hspec S).1
    (fun z hz => hymin z (mem_Feps_iff.1 hz).1 (mem_Feps_iff.1 hz).2) (hspec S).2

/-- The heated program is LP-type. -/
theorem heat_lpType {c : EuclideanSpace ℝ (Fin d)} {Θ : Set (EuclideanSpace ℝ (Fin d))}
    {Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ} {M : ℕ} {ω : Fin M → Fin L × ℝ}
    (h : HeatSpec c Θ Θk ε ω) :
    LPType (fun S => solOf c ε (Feps Θ Θk ε ω S)) (fun θ i => θ ∈ Cset Θk ε (ω i)) := by
  refine ⟨fun S z hz => (h.mem S).2 z hz, fun S T hST hf => ?_⟩
  refine (h.uniq T _ (h.mem S).1 hf fun z hz1 hz2 => ?_).symm
  exact h.opt S z hz1 fun i hi => hz2 i (hST hi)

/-- Helly: heated bases have at most `d` elements. -/
theorem heat_basis_card {c : EuclideanSpace ℝ (Fin d)} {Θ : Set (EuclideanSpace ℝ (Fin d))}
    (hΘ : Convex ℝ Θ) {Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))} (hΘk : ∀ k, Convex ℝ (Θk k))
    {ε : ℝ} (hε : 0 < ε) {M : ℕ} {ω : Fin M → Fin L × ℝ} (h : HeatSpec c Θ Θk ε ω)
    (S B : Finset (Fin M)) (hB : IsBasisOf (fun S => solOf c ε (Feps Θ Θk ε ω S)) S B) :
    B.card ≤ d := by
  obtain ⟨J', hJ'B, hJ'c, hJ'⟩ := helly_basis (fobj_convex c hε.le) (hΘ.cthickening ε)
    (C := fun i => Cset Θk ε (ω i)) (fun i => (hΘk (ω i).1).cthickening _)
    (fun S => solOf c ε (Feps Θ Θk ε ω S)) h.mem h.opt h.uniq B
  have := hB.2.2 J' hJ'B (hJ'.trans hB.2.1)
  rw [← this]; exact hJ'c

/-- Measurability of the heated solution map in the sample. -/
theorem measurable_solEps (c : EuclideanSpace ℝ (Fin d)) {Θ : Set (EuclideanSpace ℝ (Fin d))}
    (hΘ : Convex ℝ Θ) {Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))} (hΘk : ∀ k, Convex ℝ (Θk k))
    {ε : ℝ} (hε : 0 < ε) {M : ℕ} (S : Finset (Fin M))
    (hne : ∀ ω : Fin M → Fin L × ℝ, (Θ ∩ ⋂ i ∈ S, Θk (ω i).1).Nonempty) :
    Measurable (fun ω : Fin M → Fin L × ℝ => solOf c ε (Feps Θ Θk ε ω S)) := by
  have hz : ∀ q : EuclideanSpace ℝ (Fin d),
      MeasurableSet {z : Fin L × ℝ | q ∈ Cset Θk ε z} := by
    intro q
    have h1 : Measurable (fun z : Fin L × ℝ => Metric.infEDist q (Θk z.1)) :=
      (measurable_of_countable (fun k : Fin L => Metric.infEDist q (Θk k))).comp measurable_fst
    have h2 : Measurable (fun z : Fin L × ℝ => ENNReal.ofReal (rad ε z)) := by
      unfold rad; fun_prop
    simpa only [Cset, Metric.mem_cthickening_iff] using measurableSet_le h1 h2
  refine argmin_measurable c hε (fun ω => Feps Θ Θk ε ω S) (fun q => ?_)
    (fun ω => isClosed_Feps Θ Θk ε ω S) (fun ω => convex_Feps hΘ hΘk ε ω S) (fun ω => ?_) _
    (fun ω => ?_)
  · have : {ω : Fin M → Fin L × ℝ | q ∈ Feps Θ Θk ε ω S} =
        {_ω | q ∈ Metric.cthickening ε Θ} ∩ ⋂ i ∈ S, (fun ω => ω i) ⁻¹' {z | q ∈ Cset Θk ε z} := by
      ext ω; simp [Feps, Set.mem_iInter]
    rw [this]
    exact (MeasurableSet.const _).inter
      (MeasurableSet.biInter S.countable_toSet fun i _ => (measurable_pi_apply i) (hz q))
  · obtain ⟨θ0, h0⟩ := hne ω
    exact ⟨θ0, interior_maximal (ball_subset_Feps hε.le ω S h0) Metric.isOpen_ball
      (Metric.mem_ball_self hε)⟩
  · obtain ⟨θ0, h0⟩ := hne ω
    exact solOf_spec c hε (isClosed_Feps Θ Θk ε ω S)
      ⟨θ0, ball_subset_Feps hε.le ω S h0 (Metric.mem_ball_self hε)⟩

end Setting

section Null

open MeasureTheory

variable {d L : ℕ}

/-- The law of a heated point: `k ~ μk`, label `u ~ Uniform[0,1]`. -/
noncomputable def heatMeas (μk : Measure (Fin L)) : Measure (Fin L × ℝ) :=
  μk.prod (volume.restrict (Set.Icc (0:ℝ) 1))

instance isProb_restrict_Icc : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) :=
  ⟨by simp [Measure.restrict_apply_univ, Real.volume_Icc]⟩

instance (μk : Measure (Fin L)) [IsProbabilityMeasure μk] :
    IsProbabilityMeasure (heatMeas μk) := by
  unfold heatMeas; infer_instance

/-- If every one-coordinate section (through `update`) is null, the set is null. -/
theorem pi_null_of_update {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    {n : ℕ} (z : Fin (n + 1)) {A : Set (Fin (n + 1) → Z)} (hA : MeasurableSet A)
    (hsec : ∀ ω : Fin (n + 1) → Z, P {x | Function.update ω z x ∈ A} = 0) :
    Measure.pi (fun _ : Fin (n + 1) => P) A = 0 := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) z
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Z) z with he
  have hT : MeasurableSet (e.symm ⁻¹' A) := e.symm.measurable hA
  have hA' : A = e ⁻¹' (e.symm ⁻¹' A) := by ext ω; simp
  rw [hA', hmp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply_symm hT]
  refine (lintegral_congr fun y => ?_).trans lintegral_zero
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · simp [Set.eq_empty_of_isEmpty]
  · have := hsec (Fin.insertNth z (Classical.arbitrary Z) y)
    simp only [Fin.update_insertNth] at this
    show P {x | Fin.insertNth z x y ∈ A} = 0
    exact this

theorem measurable_infEDist_pair (Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × Fin L => Metric.infEDist p.1 (Θk p.2)) := by
  apply measurable_from_prod_countable_left
  intro k
  show Measurable fun x : EuclideanSpace ℝ (Fin d) => Metric.infEDist x (Θk k)
  exact (Metric.continuous_infEDist (s := Θk k)).measurable

theorem heatMeas_null_of_slices (μk : Measure (Fin L)) [IsProbabilityMeasure μk]
    {S : Set (Fin L × ℝ)} (hS : MeasurableSet S)
    (h : ∀ k, (volume : Measure ℝ) {u | (k, u) ∈ S} = 0) : heatMeas μk S = 0 := by
  unfold heatMeas
  rw [Measure.prod_apply hS]
  refine (lintegral_congr fun k => ?_).trans lintegral_zero
  exact le_antisymm ((Measure.le_iff'.1 Measure.restrict_le_self _).trans (h k).le) bot_le

/-- A level set `ofReal (ε (1 + |u|)) = D` has at most two points. -/
theorem volume_rad_eq (ε : ℝ) (hε : 0 < ε) (D : ENNReal) :
    (volume : Measure ℝ) {u | D = ENNReal.ofReal (ε * (1 + |u|))} = 0 := by
  set a := D.toReal / ε - 1
  have hsub : {u : ℝ | D = ENNReal.ofReal (ε * (1 + |u|))} ⊆ {a, -a} := by
    intro u hu
    simp only [Set.mem_setOf_eq] at hu
    have hpos : 0 ≤ ε * (1 + |u|) := by positivity
    have h1 : D.toReal = ε * (1 + |u|) := by rw [hu, ENNReal.toReal_ofReal hpos]
    have h2 : |u| = a := by
      simp only [a, h1]; field_simp; ring
    rcases abs_eq (h2 ▸ abs_nonneg u) |>.1 h2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact measure_mono_null hsub ((Set.toFinite {a, -a}).measure_zero volume)

variable (c : EuclideanSpace ℝ (Fin d)) {Θ : Set (EuclideanSpace ℝ (Fin d))}
  {Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))}

theorem Feps_update_of_not_mem (ε : ℝ) {M : ℕ} (ω : Fin M → Fin L × ℝ) (S : Finset (Fin M))
    {z : Fin M} (hz : z ∉ S) (x : Fin L × ℝ) :
    Feps Θ Θk ε (Function.update ω z x) S = Feps Θ Θk ε ω S := by
  ext y
  simp only [Feps, Set.mem_inter_iff, Set.mem_iInter]
  refine and_congr_right fun _ => forall₂_congr fun i hi => ?_
  rw [Function.update_of_ne (fun h => hz (by rw [← h]; exact hi))]

/-- D5b: a.s. no ties between a sub-sample's heated solution and an outside constraint. -/
theorem ae_noTie (hΘ : Convex ℝ Θ) (hΘk : ∀ k, Convex ℝ (Θk k)) {ε : ℝ} (hε : 0 < ε)
    (μk : Measure (Fin L)) [IsProbabilityMeasure μk] {M : ℕ} (B : Finset (Fin M))
    (hne : ∀ ω : Fin M → Fin L × ℝ, (Θ ∩ ⋂ i ∈ B, Θk (ω i).1).Nonempty)
    (z : Fin M) (hz : z ∉ B) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Fin M => heatMeas μk),
      Metric.infEDist (solOf c ε (Feps Θ Θk ε ω B)) (Θk (ω z).1) ≠ ENNReal.ofReal (rad ε (ω z)) := by
  cases M with
  | zero => exact Fin.elim0 z
  | succ n =>
    rw [ae_iff]
    simp only [ne_eq, not_not]
    have hs := measurable_solEps c hΘ hΘk hε B hne
    have hG := measurable_infEDist_pair Θk
    apply pi_null_of_update _ z
    · refine measurableSet_eq_fun (hG.comp (hs.prodMk ((measurable_pi_apply z).fst))) ?_
      unfold rad; fun_prop
    · intro ω
      have hset : {x : Fin L × ℝ | Function.update ω z x ∈ {ω' : Fin (n + 1) → Fin L × ℝ |
          Metric.infEDist (solOf c ε (Feps Θ Θk ε ω' B)) (Θk (ω' z).1) =
            ENNReal.ofReal (rad ε (ω' z))}} =
          {x | Metric.infEDist (solOf c ε (Feps Θ Θk ε ω B)) (Θk x.1) =
            ENNReal.ofReal (rad ε x)} := by
        ext x
        simp only [Set.mem_setOf_eq, Feps_update_of_not_mem ε ω B hz x, Function.update_self]
      rw [hset]
      refine heatMeas_null_of_slices μk ?_ fun k => ?_
      · refine measurableSet_eq_fun ?_ ?_
        · exact (measurable_of_countable (fun k : Fin L =>
            Metric.infEDist (solOf c ε (Feps Θ Θk ε ω B)) (Θk k))).comp measurable_fst
        · unfold rad; fun_prop
      · simpa [rad] using volume_rad_eq ε hε
          (Metric.infEDist (solOf c ε (Feps Θ Θk ε ω B)) (Θk k))

/-- D5b': labels are a.s. distinct. -/
theorem ae_label_ne (μk : Measure (Fin L)) [IsProbabilityMeasure μk] {M : ℕ} (i j : Fin M)
    (hij : i ≠ j) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Fin M => heatMeas μk), (ω i).2 ≠ (ω j).2 := by
  cases M with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [ae_iff]
    simp only [ne_eq, not_not]
    apply pi_null_of_update _ j
    · exact measurableSet_eq_fun ((measurable_pi_apply i).snd) ((measurable_pi_apply j).snd)
    · intro ω
      have hset : {x : Fin L × ℝ | Function.update ω j x ∈
          {ω' : Fin (n + 1) → Fin L × ℝ | (ω' i).2 = (ω' j).2}} = {x | (ω i).2 = x.2} := by
        ext x
        simp [Function.update_of_ne hij]
      rw [hset]
      refine heatMeas_null_of_slices μk (measurableSet_eq_fun measurable_const measurable_snd)
        fun k => ?_
      have : {u : ℝ | ((k, u) : Fin L × ℝ) ∈ {x : Fin L × ℝ | (ω i).2 = x.2}} = {(ω i).2} := by
        ext u; simp [eq_comm]
      rw [this]; exact measure_singleton _

end Null

section Converge

open Filter Topology

variable {d : ℕ}

/-- D7 (convergence): minimisers of the perturbed objective over shrinking supersets of the
original feasible set converge to the unique original minimiser. -/
theorem tendsto_heated (c : EuclideanSpace ℝ (Fin d)) {F : Set (EuclideanSpace ℝ (Fin d))}
    {Fn : ℕ → Set (EuclideanSpace ℝ (Fin d))} {εn : ℕ → ℝ} (hεpos : ∀ n, 0 < εn n)
    (hε0 : Tendsto εn atTop (𝓝 0)) (hsub : ∀ n, F ⊆ Fn n) (hconv : ∀ n, Convex ℝ (Fn n))
    (hlim : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ (y : ℕ → EuclideanSpace ℝ (Fin d)) (y0 : _),
      (∀ k, y k ∈ Fn (φ k)) → Tendsto y atTop (𝓝 y0) → y0 ∈ F)
    {θs : EuclideanSpace ℝ (Fin d)} (hθs : θs ∈ F)
    (huniq : ∀ y ∈ F, inner ℝ c y ≤ inner ℝ c θs → y = θs)
    (x : ℕ → EuclideanSpace ℝ (Fin d))
    (hx : ∀ n, x n ∈ Fn n ∧ ∀ y ∈ Fn n, fobj c (εn n) (x n) ≤ fobj c (εn n) y) :
    Tendsto x atTop (𝓝 θs) := by
  by_contra hcon
  rw [Metric.tendsto_atTop] at hcon
  push_neg at hcon
  obtain ⟨δ, hδ, hfreq⟩ := hcon
  have hfr : ∃ᶠ n in atTop, δ ≤ dist (x n) θs :=
    frequently_atTop.2 fun N => by obtain ⟨n, hn, h⟩ := hfreq N; exact ⟨n, hn, h⟩
  obtain ⟨φ, hφ, hφd⟩ := extraction_of_frequently_atTop hfr
  -- the point at distance δ from θs on the segment towards x (φ k)
  set lam : ℕ → ℝ := fun k => δ / dist (x (φ k)) θs with hlam
  have hdpos : ∀ k, 0 < dist (x (φ k)) θs := fun k => lt_of_lt_of_le hδ (hφd k)
  have hlam0 : ∀ k, 0 < lam k := fun k => div_pos hδ (hdpos k)
  have hlam1 : ∀ k, lam k ≤ 1 := fun k => (div_le_one (hdpos k)).2 (hφd k)
  set y : ℕ → EuclideanSpace ℝ (Fin d) := fun k => θs + lam k • (x (φ k) - θs) with hy
  have hyF : ∀ k, y k ∈ Fn (φ k) := fun k =>
    (hconv (φ k)).add_smul_sub_mem (hsub _ hθs) (hx (φ k)).1 ⟨(hlam0 k).le, hlam1 k⟩
  have hyd : ∀ k, y k ∈ Metric.sphere θs δ := by
    intro k
    rw [Metric.mem_sphere, hy, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hlam0 k).le]
    rw [← dist_eq_norm, hlam, div_mul_cancel₀ _ (hdpos k).ne']
  -- cost bound along the subsequence
  have hcost : ∀ k, inner ℝ c (y k) ≤ inner ℝ c θs + εn (φ k) * ‖θs‖ ^ 2 := by
    intro k
    have h1 := (hx (φ k)).2 θs (hsub _ hθs)
    unfold fobj at h1
    have h2 : inner ℝ c (x (φ k)) ≤ inner ℝ c θs + εn (φ k) * ‖θs‖ ^ 2 := by
      nlinarith [hεpos (φ k), sq_nonneg ‖x (φ k)‖]
    have h3 : inner ℝ c (y k) = (1 - lam k) * inner ℝ c θs + lam k * inner ℝ c (x (φ k)) := by
      simp only [hy, inner_add_right, real_inner_smul_right, inner_sub_right]; ring
    rw [h3]
    have h4 : 0 ≤ εn (φ k) * ‖θs‖ ^ 2 := by have := hεpos (φ k); positivity
    nlinarith [hlam0 k, hlam1 k]
  obtain ⟨y0, hy0s, ψ, hψ, hψt⟩ := (isCompact_sphere θs δ).tendsto_subseq hyd
  have hy0F : y0 ∈ F := hlim (φ ∘ ψ) (hφ.comp hψ) (y ∘ ψ) y0 (fun k => hyF (ψ k)) hψt
  have hεt : Tendsto (fun k => εn (φ (ψ k))) atTop (𝓝 0) :=
    hε0.comp ((hφ.comp hψ).tendsto_atTop)
  have hc0 : inner ℝ c y0 ≤ inner ℝ c θs := by
    have hl : Tendsto (fun k => inner ℝ c (y (ψ k))) atTop (𝓝 (inner ℝ c y0)) :=
      ((continuous_const.inner continuous_id).tendsto y0).comp hψt
    have hr : Tendsto (fun k => inner ℝ c θs + εn (φ (ψ k)) * ‖θs‖ ^ 2) atTop
        (𝓝 (inner ℝ c θs + 0 * ‖θs‖ ^ 2)) :=
      tendsto_const_nhds.add (hεt.mul tendsto_const_nhds)
    rw [zero_mul, add_zero] at hr
    exact le_of_tendsto_of_tendsto' hl hr fun k => hcost (ψ k)
  have := huniq y0 hy0F hc0
  rw [this, Metric.mem_sphere, dist_self] at hy0s
  exact hδ.ne' hy0s.symm

/-- Limits of points of shrinking closed thickenings lie in the (closed) set. -/
theorem mem_of_tendsto_cthickening {A : Set (EuclideanSpace ℝ (Fin d))} (hA : IsClosed A)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) {y : ℕ → EuclideanSpace ℝ (Fin d)} {y0 : _}
    (hy : ∀ k, y k ∈ Metric.cthickening (r k) A) (ht : Tendsto y atTop (𝓝 y0)) : y0 ∈ A := by
  rw [← hA.closure_eq, Metric.mem_closure_iff_infEDist_zero]
  have h1 : Tendsto (fun k => Metric.infEDist (y k) A) atTop (𝓝 (Metric.infEDist y0 A)) :=
    (Metric.continuous_infEDist.tendsto y0).comp ht
  have h2 : Tendsto (fun k => ENNReal.ofReal (r k)) atTop (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hr
    rw [ENNReal.ofReal_zero] at this
    exact this
  exact le_antisymm (le_of_tendsto_of_tendsto' h1 h2 fun k => Metric.mem_cthickening_iff.1 (hy k))
    bot_le

end Converge



open MeasureTheory

section Exch

variable {Pt : Type*} [MeasurableSpace Pt] (P : Measure Pt) [IsProbabilityMeasure P]

theorem pi_sum_good {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (R : Set (ι → Pt)) (hR : MeasurableSet R) (G : Set ((ι → Pt) × Pt)) (hG : MeasurableSet G) :
    Measure.pi (fun _ : ι ⊕ κ => P)
      {g | (fun i => g (.inl i)) ∈ R ∧ ∀ j, ((fun i => g (.inl i)), g (.inr j)) ∈ G} =
      ∫⁻ a in R, P {x | (a, x) ∈ G} ^ Fintype.card κ ∂(Measure.pi fun _ : ι => P) := by
  have hmp := measurePreserving_sumPiEquivProdPi (X := fun _ : ι ⊕ κ => Pt)
    (fun _ : ι ⊕ κ => P)
  set T : Set ((ι → Pt) × (κ → Pt)) := {p | p.1 ∈ R ∧ ∀ j, (p.1, p.2 j) ∈ G} with hT
  have hTm : MeasurableSet T := by
    have : T = (Prod.fst ⁻¹' R) ∩
        ⋂ j, (fun p : (ι → Pt) × (κ → Pt) => (p.1, p.2 j)) ⁻¹' G := by
      ext p; simp [hT]
    rw [this]
    exact (measurable_fst hR).inter (MeasurableSet.iInter fun j =>
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)) hG)
  have hpre : {g : ι ⊕ κ → Pt | (fun i => g (.inl i)) ∈ R ∧
      ∀ j, ((fun i => g (.inl i)), g (.inr j)) ∈ G} =
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => Pt)) ⁻¹' T := by
    ext g; simp [hT, MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
  rw [hpre, hmp.measure_preimage_equiv, Measure.prod_apply hTm, ← lintegral_indicator hR]
  refine lintegral_congr fun a => ?_
  by_cases ha : a ∈ R
  · have hset : (Prod.mk a ⁻¹' T) = Set.pi Set.univ fun _ : κ => {x | (a, x) ∈ G} := by
      ext b; simp [hT, ha]
    rw [hset, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Set.indicator_of_mem ha]
  · have hset : (Prod.mk a ⁻¹' T) = ∅ := by
      ext b; simp [hT, ha]
    rw [hset, measure_empty, Set.indicator_of_notMem ha]

theorem pi_good_eq {M d : ℕ} (I : Finset (Fin M)) (hI : I.card = d)
    (e : Fin d ≃ {x // x ∈ I}) (R : Set (Fin d → Pt)) (hR : MeasurableSet R)
    (G : Set ((Fin d → Pt) × Pt)) (hG : MeasurableSet G) :
    Measure.pi (fun _ : Fin M => P)
      {ω | (fun i => ω (e i)) ∈ R ∧ ∀ z, z ∉ I → ((fun i => ω (e i)), ω z) ∈ G} =
      ∫⁻ a in R, P {x | (a, x) ∈ G} ^ (M - d) ∂(Measure.pi fun _ : Fin d => P) := by
  classical
  set σ : Fin d ⊕ {x // x ∉ I} ≃ Fin M :=
    (Equiv.sumCongr e (Equiv.refl {x // x ∉ I})).trans (Equiv.sumCompl (· ∈ I)) with hσ
  have hmp := measurePreserving_piCongrLeft (fun _ : Fin M => P) σ
  rw [← hmp.measure_preimage_equiv]
  have hpre : (MeasurableEquiv.piCongrLeft (fun _ : Fin M => Pt) σ) ⁻¹'
      {ω | (fun i => ω (e i)) ∈ R ∧ ∀ z, z ∉ I → ((fun i => ω (e i)), ω z) ∈ G} =
      {g | (fun i => g (.inl i)) ∈ R ∧ ∀ j, ((fun i => g (.inl i)), g (.inr j)) ∈ G} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    have hap : ∀ s, (MeasurableEquiv.piCongrLeft (fun _ : Fin M => Pt) σ g) (σ s) = g s :=
      fun s => MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin M => Pt) σ g s
    have he : ∀ i, (MeasurableEquiv.piCongrLeft (fun _ : Fin M => Pt) σ g) (e i) =
        g (.inl i) := fun i => by
      have := hap (.inl i); simpa [hσ] using this
    simp only [he]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h j
      have := h j.1 j.2
      have h2 := hap (.inr j)
      simp only [hσ, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
        Equiv.sumCompl_apply_inr] at h2
      rwa [h2] at this
    · intro h z hz
      have := h ⟨z, hz⟩
      have h2 := hap (.inr ⟨z, hz⟩)
      simp only [hσ, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
        Equiv.sumCompl_apply_inr] at h2
      rwa [h2]
  have hcard : Fintype.card {x // x ∉ I} = M - d := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hI, Fintype.card_fin]
  rw [hpre, ← hcard]
  exact pi_sum_good P R hR G hG

end Exch


section D6

open MeasureTheory
open scoped ENNReal

variable {d L : ℕ}

theorem isBasisOf_map {α β X : Type*} [DecidableEq α] [DecidableEq β] (sol : Finset α → X)
    (ι : β ↪ α) (S B : Finset β) :
    IsBasisOf sol (S.map ι) (B.map ι) ↔ IsBasisOf (fun T => sol (T.map ι)) S B := by
  unfold IsBasisOf
  refine and_congr Finset.map_subset_map (and_congr Iff.rfl ⟨fun h B' hB' hs => ?_, fun h C hC hs => ?_⟩)
  · exact (Finset.map_inj).1 (h _ (Finset.map_subset_map.2 hB') hs)
  · obtain ⟨u, hu, rfl⟩ := Finset.subset_map_iff.1 hC
    rw [h u hu hs]

theorem eq_map_of_isBasisOf {α β X : Type*} [DecidableEq α] (sol : Finset α → X)
    (ι : β ↪ α) {S : Finset β} {B : Finset α} (hB : IsBasisOf sol (S.map ι) B) :
    ∃ B' : Finset β, B = B'.map ι := by
  obtain ⟨u, -, hu⟩ := Finset.subset_map_iff.1 hB.1
  exact ⟨u, hu⟩

theorem Feps_map (Θ : Set (EuclideanSpace ℝ (Fin d))) (Θk : Fin L → Set (EuclideanSpace ℝ (Fin d)))
    (ε : ℝ) {M m : ℕ} (ω : Fin M → Fin L × ℝ) (ι : Fin m ↪ Fin M) (S : Finset (Fin m)) :
    Feps Θ Θk ε ω (S.map ι) = Feps Θ Θk ε (ω ∘ ι) S := by
  ext y
  simp only [mem_Feps_iff, Finset.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Function.comp_apply]

/-- The heated solution map of a sample. -/
noncomputable def solH (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) {M : ℕ} (ω : Fin M → Fin L × ℝ)
    (S : Finset (Fin M)) : EuclideanSpace ℝ (Fin d) :=
  solOf c ε (Feps Θ Θk ε ω S)

/-- `x` does not conflict with the `m`-point sample `a`. -/
def GoodL (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) {m : ℕ} (a : Fin m → Fin L × ℝ)
    (x : Fin L × ℝ) : Prop :=
  solH c Θ Θk ε a Finset.univ ∈ Cset Θk ε x ∧
    ∀ B, IsBasisOf (solH c Θ Θk ε a) Finset.univ B → ∀ w, w ∉ B → x.2 < (a w).2

variable (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
  (Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ)

theorem solH_map {M m : ℕ} (ω : Fin M → Fin L × ℝ) (ι : Fin m ↪ Fin M) (T : Finset (Fin m)) :
    solH c Θ Θk ε ω (T.map ι) = solH c Θ Θk ε (ω ∘ ι) T := by
  unfold solH; rw [Feps_map]

theorem good_iff_goodL {M m : ℕ} (ω : Fin M → Fin L × ℝ) (ι : Fin m ↪ Fin M) (z : Fin M) :
    Good (sol := solH c Θ Θk ε ω) (feas := fun θ i => θ ∈ Cset Θk ε (ω i)) (fun i => (ω i).2)
      (Finset.univ.map ι) z ↔ GoodL c Θ Θk ε (ω ∘ ι) (ω z) := by
  have hsol : (fun T => solH c Θ Θk ε ω (T.map ι)) = solH c Θ Θk ε (ω ∘ ι) := by
    funext T; exact solH_map c Θ Θk ε ω ι T
  unfold Good GoodL
  refine and_congr (by rw [solH_map]) ⟨fun h B hB w hw => ?_, fun h B hB w hw => ?_⟩
  · rw [← hsol] at hB
    have hw' : ι w ∈ Finset.univ.map ι \ B.map ι := by
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_map_of_mem _ (Finset.mem_univ w), fun h' => hw
        ((Finset.mem_map' ι).1 h')⟩
    simpa using h (B.map ι) ((isBasisOf_map _ ι _ _).2 hB) (ι w) hw'
  · obtain ⟨B', rfl⟩ := eq_map_of_isBasisOf _ ι hB
    rw [isBasisOf_map, hsol] at hB
    rw [Finset.mem_sdiff] at hw
    obtain ⟨w', -, rfl⟩ := Finset.mem_map.1 hw.1
    have hw' : w' ∉ B' := fun h' => hw.2 (Finset.mem_map_of_mem _ h')
    simpa using h B' hB w' hw'

variable {c Θ Θk ε}

theorem hne_of (hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θk k).Nonempty) {M : ℕ}
    (ω : Fin M → Fin L × ℝ) (S : Finset (Fin M)) : (Θ ∩ ⋂ i ∈ S, Θk (ω i).1).Nonempty := by
  classical
  obtain ⟨θ, hθ, hθT⟩ := hne0 (S.image fun i => (ω i).1)
  refine ⟨θ, hθ, ?_⟩
  simp only [Set.mem_iInter] at hθT ⊢
  intro i hi
  exact hθT _ (Finset.mem_image_of_mem _ hi)

theorem measurableSet_goodL (hΘ : Convex ℝ Θ) (hΘk : ∀ k, Convex ℝ (Θk k)) (hε : 0 < ε)
    (hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θk k).Nonempty) (m : ℕ) :
    MeasurableSet {p : (Fin m → Fin L × ℝ) × (Fin L × ℝ) | GoodL c Θ Θk ε p.1 p.2} := by
  have hs : ∀ S, Measurable fun p : (Fin m → Fin L × ℝ) × (Fin L × ℝ) => solH c Θ Θk ε p.1 S :=
    fun S => (measurable_solEps c hΘ hΘk hε S (fun ω => hne_of hne0 ω S)).comp measurable_fst
  have hEq : ∀ S S', Measurable fun p : (Fin m → Fin L × ℝ) × (Fin L × ℝ) =>
      solH c Θ Θk ε p.1 S = solH c Θ Θk ε p.1 S' :=
    fun S S' => measurableSet_setOfPred.1 (measurableSet_eq_fun (hs S) (hs S'))
  have hC : Measurable fun p : (Fin m → Fin L × ℝ) × (Fin L × ℝ) =>
      solH c Θ Θk ε p.1 Finset.univ ∈ Cset Θk ε p.2 := by
    refine measurableSet_setOfPred.1 ?_
    simp only [Cset, Metric.mem_cthickening_iff]
    refine measurableSet_le ((measurable_infEDist_pair Θk).comp ((hs _).prodMk measurable_snd.fst)) ?_
    unfold rad; fun_prop
  have hB : ∀ B : Finset (Fin m), Measurable fun p : (Fin m → Fin L × ℝ) × (Fin L × ℝ) =>
      IsBasisOf (solH c Θ Θk ε p.1) Finset.univ B := by
    intro B
    unfold IsBasisOf
    exact measurable_const.and ((hEq _ _).and (Measurable.forall fun B' =>
      measurable_const.imp ((hEq _ _).imp measurable_const)))
  refine measurableSet_setOfPred.2 (hC.and (Measurable.forall fun B => (hB B).imp
    (Measurable.forall fun w => measurable_const.imp ?_)))
  exact measurableSet_setOfPred.1
    (measurableSet_lt measurable_snd.snd ((measurable_pi_apply w).comp measurable_fst).snd)

theorem mem_interior_Cset {x : EuclideanSpace ℝ (Fin d)} {z : Fin L × ℝ}
    (h : Metric.infEDist x (Θk z.1) ≠ ENNReal.ofReal (rad ε z)) (hx : x ∈ Cset Θk ε z) :
    x ∈ interior (Cset Θk ε z) := by
  have hlt : Metric.infEDist x (Θk z.1) < ENNReal.ofReal (rad ε z) :=
    lt_of_le_of_ne (Metric.mem_cthickening_iff.1 hx) h
  exact interior_maximal (Metric.thickening_subset_cthickening _ _) Metric.isOpen_thickening
    (Metric.mem_thickening_iff_infEDist_lt.2 hlt)

theorem ae_nondeg (hΘ : Convex ℝ Θ) (hΘk : ∀ k, Convex ℝ (Θk k)) (hε : 0 < ε)
    (hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θk k).Nonempty)
    (μk : Measure (Fin L)) [IsProbabilityMeasure μk] (M : ℕ) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Fin M => heatMeas μk),
      Nondeg (solH c Θ Θk ε ω) Finset.univ := by
  have h : ∀ᵐ ω ∂(Measure.pi fun _ : Fin M => heatMeas μk), ∀ B : Finset (Fin M), ∀ z : Fin M,
      z ∉ B → Metric.infEDist (solH c Θ Θk ε ω B) (Θk (ω z).1) ≠
        ENNReal.ofReal (rad ε (ω z)) := by
    rw [ae_all_iff]; intro B; rw [ae_all_iff]; intro z
    by_cases hz : z ∈ B
    · exact Filter.Eventually.of_forall fun ω h => absurd hz h
    · filter_upwards [ae_noTie c hΘ hΘk hε μk B (fun ω => hne_of hne0 ω B) z hz] with ω hω _
      exact hω
  filter_upwards [h] with ω hω
  have hsp := heatSpec c hΘ hΘk hε ω (fun S => hne_of hne0 ω S)
  exact basis_unique_of_noTie (fobj_convex c hε.le) (hΘ.cthickening ε)
    (C := fun i => Cset Θk ε (ω i)) (fun i => (hΘk (ω i).1).cthickening _)
    (solH c Θ Θk ε ω) hsp.mem hsp.opt hsp.uniq Finset.univ
    (fun B _ z _ hzB hmem => mem_interior_Cset (hω B z hzB) hmem)

/-- The embedding `Fin d ↪ Fin M` enumerating a `d`-set. -/
def ιOf {M : ℕ} (I : Finset (Fin M)) (hI : I.card = d) : Fin d ↪ Fin M :=
  ⟨fun i => ((I.orderIsoOfFin hI) i).1, fun i j h =>
    (I.orderIsoOfFin hI).injective (Subtype.ext h)⟩

theorem map_ιOf {M : ℕ} (I : Finset (Fin M)) (hI : I.card = d) :
    Finset.univ.map (ιOf I hI) = I := by
  ext z
  constructor
  · intro h
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 h
    exact ((I.orderIsoOfFin hI) i).2
  · intro hz
    refine Finset.mem_map.2 ⟨(I.orderIsoOfFin hI).symm ⟨z, hz⟩, Finset.mem_univ _, ?_⟩
    show ((I.orderIsoOfFin hI) ((I.orderIsoOfFin hI).symm ⟨z, hz⟩)).1 = z
    rw [OrderIso.apply_symm_apply]

theorem isPad_iff_goodL (hΘ : Convex ℝ Θ) (hΘk : ∀ k, Convex ℝ (Θk k)) (hε : 0 < ε)
    (hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θk k).Nonempty) {M : ℕ}
    (ω : Fin M → Fin L × ℝ) (hnd : Nondeg (solH c Θ Θk ε ω) Finset.univ)
    (I : Finset (Fin M)) (ι : Fin d ↪ Fin M) (hI : Finset.univ.map ι = I) :
    IsPad (sol := solH c Θ Θk ε ω) d (fun i => (ω i).2) Finset.univ I ↔
      ∀ z, z ∉ I → GoodL c Θ Θk ε (ω ∘ ι) (ω z) := by
  have hlp : LPType (solH c Θ Θk ε ω) (fun θ i => θ ∈ Cset Θk ε (ω i)) :=
    heat_lpType (heatSpec c hΘ hΘk hε ω (fun S => hne_of hne0 ω S))
  rw [hlp.isPad_iff hnd _ (Finset.subset_univ _) (Finset.subset_univ _)]
  have hcard : I.card = d := by
    rw [← hI, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  subst hI
  simp only [hcard, true_and, Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact forall_congr' fun z => imp_congr_right fun _ => good_iff_goodL c Θ Θk ε ω ι z

theorem pad_ae_eq (hΘ : Convex ℝ Θ) (hΘk : ∀ k, Convex ℝ (Θk k)) (hε : 0 < ε)
    (hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θk k).Nonempty)
    (μk : Measure (Fin L)) [IsProbabilityMeasure μk] {M : ℕ} (I : Finset (Fin M))
    (hI : I.card = d) (R : Set (Fin d → Fin L × ℝ)) :
    {ω : Fin M → Fin L × ℝ | IsPad (sol := solH c Θ Θk ε ω) d (fun i => (ω i).2) Finset.univ I ∧
        ω ∘ ιOf I hI ∈ R} =ᵐ[Measure.pi fun _ : Fin M => heatMeas μk]
      {ω | ω ∘ ιOf I hI ∈ R ∧ ∀ z, z ∉ I → GoodL c Θ Θk ε (ω ∘ ιOf I hI) (ω z)} := by
  rw [Filter.eventuallyEq_set]
  filter_upwards [ae_nondeg (c := c) hΘ hΘk hε hne0 μk M] with ω hnd
  rw [isPad_iff_goodL hΘ hΘk hε hne0 ω hnd I (ιOf I hI) (map_ιOf I hI)]
  exact and_comm

theorem measurableSet_A (hΘ : Convex ℝ Θ) (hΘk : ∀ k, Convex ℝ (Θk k)) (hε : 0 < ε)
    (hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θk k).Nonempty) {M : ℕ} (I : Finset (Fin M))
    (ι : Fin d ↪ Fin M) (R : Set (Fin d → Fin L × ℝ)) (hR : MeasurableSet R) :
    MeasurableSet {ω : Fin M → Fin L × ℝ | ω ∘ ι ∈ R ∧
      ∀ z, z ∉ I → GoodL c Θ Θk ε (ω ∘ ι) (ω z)} := by
  have hc : Measurable fun ω : Fin M → Fin L × ℝ => ω ∘ ι :=
    measurable_pi_iff.2 fun i => measurable_pi_apply (ι i)
  have : {ω : Fin M → Fin L × ℝ | ω ∘ ι ∈ R ∧ ∀ z, z ∉ I → GoodL c Θ Θk ε (ω ∘ ι) (ω z)} =
      (fun ω : Fin M → Fin L × ℝ => ω ∘ ι) ⁻¹' R ∩
      ⋂ z ∈ (Iᶜ : Finset (Fin M)), (fun ω : Fin M → Fin L × ℝ => (ω ∘ ι, ω z)) ⁻¹'
        {p : (Fin d → Fin L × ℝ) × (Fin L × ℝ) | GoodL c Θ Θk ε p.1 p.2} := by
    ext ω; simp
  rw [this]
  exact (hc hR).inter (MeasurableSet.biInter (Set.toFinite _).countable fun z _ =>
    (hc.prodMk (measurable_pi_apply z)) (measurableSet_goodL (c := c) hΘ hΘk hε hne0 d))

/-- (L1) exchangeability: the probability that `I` is the padded set (jointly with a condition
on the points of `I`). -/
theorem pad_measure (hΘ : Convex ℝ Θ) (hΘk : ∀ k, Convex ℝ (Θk k)) (hε : 0 < ε)
    (hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θk k).Nonempty)
    (μk : Measure (Fin L)) [IsProbabilityMeasure μk] {M : ℕ} (I : Finset (Fin M))
    (hI : I.card = d) (R : Set (Fin d → Fin L × ℝ)) (hR : MeasurableSet R) :
    Measure.pi (fun _ : Fin M => heatMeas μk)
      {ω | IsPad (sol := solH c Θ Θk ε ω) d (fun i => (ω i).2) Finset.univ I ∧
        ω ∘ ιOf I hI ∈ R} =
      ∫⁻ a in R, heatMeas μk {x | GoodL c Θ Θk ε a x} ^ (M - d)
        ∂(Measure.pi fun _ : Fin d => heatMeas μk) := by
  rw [measure_congr (pad_ae_eq (c := c) hΘ hΘk hε hne0 μk I hI R)]
  exact pi_good_eq (heatMeas μk) I hI (I.orderIsoOfFin hI).toEquiv R hR
    {p | GoodL c Θ Θk ε p.1 p.2} (measurableSet_goodL (c := c) hΘ hΘk hε hne0 d)

theorem nullMeasurableSet_pad (hΘ : Convex ℝ Θ) (hΘk : ∀ k, Convex ℝ (Θk k)) (hε : 0 < ε)
    (hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θk k).Nonempty)
    (μk : Measure (Fin L)) [IsProbabilityMeasure μk] {M : ℕ} (I : Finset (Fin M))
    (hI : I.card = d) :
    NullMeasurableSet
      {ω : Fin M → Fin L × ℝ | IsPad (sol := solH c Θ Θk ε ω) d (fun i => (ω i).2) Finset.univ I}
      (Measure.pi fun _ : Fin M => heatMeas μk) := by
  have h := pad_ae_eq (c := c) hΘ hΘk hε hne0 μk I hI Set.univ
  simp only [Set.mem_univ, and_true, true_and] at h
  exact (measurableSet_A (c := c) hΘ hΘk hε hne0 I (ιOf I hI) Set.univ MeasurableSet.univ
    |>.nullMeasurableSet.congr (by simpa using h.symm))

theorem ae_injOn_label (μk : Measure (Fin L)) [IsProbabilityMeasure μk] (M : ℕ) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Fin M => heatMeas μk),
      Set.InjOn (fun i => (ω i).2) (Finset.univ : Finset (Fin M)) := by
  have h : ∀ᵐ ω ∂(Measure.pi fun _ : Fin M => heatMeas μk), ∀ i j : Fin M,
      i ≠ j → (ω i).2 ≠ (ω j).2 := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun ω h => absurd hij h
    · filter_upwards [ae_label_ne μk i j hij] with ω hω _ using hω
  filter_upwards [h] with ω hω
  intro i _ j _ hij
  by_contra hne
  exact hω i j hne hij

/-- (Σ) a.s. exactly one padded `d`-set. -/
theorem sum_pad (hΘ : Convex ℝ Θ) (hΘk : ∀ k, Convex ℝ (Θk k)) (hε : 0 < ε)
    (hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θk k).Nonempty)
    (μk : Measure (Fin L)) [IsProbabilityMeasure μk] {M : ℕ} (hM : d ≤ M) :
    ∑ I ∈ (Finset.univ : Finset (Fin M)).powersetCard d,
      Measure.pi (fun _ : Fin M => heatMeas μk)
        {ω | IsPad (sol := solH c Θ Θk ε ω) d (fun i => (ω i).2) Finset.univ I} = 1 := by
  set Pm := Measure.pi fun _ : Fin M => heatMeas μk
  set A : Finset (Fin M) → Set (Fin M → Fin L × ℝ) := fun I =>
    {ω | IsPad (sol := solH c Θ Θk ε ω) d (fun i => (ω i).2) Finset.univ I} with hA
  have hnm : ∀ I ∈ (Finset.univ : Finset (Fin M)).powersetCard d, NullMeasurableSet (A I) Pm :=
    fun I hI => nullMeasurableSet_pad hΘ hΘk hε hne0 μk I (Finset.mem_powersetCard.1 hI).2
  have hae : ∀ᵐ ω ∂Pm, ∑ I ∈ (Finset.univ : Finset (Fin M)).powersetCard d,
      (A I).indicator 1 ω = (1 : ℝ≥0∞) := by
    filter_upwards [ae_nondeg (c := c) hΘ hΘk hε hne0 μk M, ae_injOn_label μk M] with ω hnd hinj
    have hsp := heatSpec c hΘ hΘk hε ω (fun S => hne_of hne0 ω S)
    obtain ⟨I0, hI0⟩ := exists_isPad (sol := solH c Θ Θk ε ω) (d := d) (fun i => (ω i).2) hinj
      (by rw [Finset.card_univ, Fintype.card_fin]; exact hM)
      (fun B hB => heat_basis_card hΘ hΘk hε hsp Finset.univ B hB)
    have hI0c : I0.card = d := by obtain ⟨_, _, _, _, hc, _⟩ := hI0; exact hc
    rw [Finset.sum_eq_single I0]
    · simp [hA, Set.indicator, hI0]
    · intro I _ hne
      simp only [hA, Set.indicator, Set.mem_setOf_eq]
      rw [if_neg]
      exact fun hI => hne (isPad_unique hnd _ (Finset.subset_univ _) hI hI0)
    · intro h
      exact absurd (Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hI0c⟩) h
  calc ∑ I ∈ (Finset.univ : Finset (Fin M)).powersetCard d, Pm (A I)
      = ∑ I ∈ (Finset.univ : Finset (Fin M)).powersetCard d, ∫⁻ ω, (A I).indicator 1 ω ∂Pm :=
        Finset.sum_congr rfl fun I hI => (lintegral_indicator_one₀ (hnm I hI)).symm
    _ = ∫⁻ ω, ∑ I ∈ (Finset.univ : Finset (Fin M)).powersetCard d, (A I).indicator 1 ω ∂Pm :=
        (lintegral_finset_sum' _ fun I hI => aemeasurable_const.indicator₀ (hnm I hI)).symm
    _ = ∫⁻ _, 1 ∂Pm := lintegral_congr_ae hae
    _ = 1 := by simp [Pm]

/-- `C(M,d) Φ(M-d) = 1`. -/
theorem choose_mul_phi (hΘ : Convex ℝ Θ) (hΘk : ∀ k, Convex ℝ (Θk k)) (hε : 0 < ε)
    (hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θk k).Nonempty)
    (μk : Measure (Fin L)) [IsProbabilityMeasure μk] {M : ℕ} (hM : d ≤ M) :
    (M.choose d : ℝ≥0∞) * ∫⁻ a, heatMeas μk {x | GoodL c Θ Θk ε a x} ^ (M - d)
        ∂(Measure.pi fun _ : Fin d => heatMeas μk) = 1 := by
  have h := sum_pad (c := c) hΘ hΘk hε hne0 μk hM
  rw [Finset.sum_congr rfl (g := fun _ => ∫⁻ a, heatMeas μk {x | GoodL c Θ Θk ε a x} ^ (M - d)
        ∂(Measure.pi fun _ : Fin d => heatMeas μk)) ?_] at h
  · rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    exact h
  · intro I hI
    have hIc := (Finset.mem_powersetCard.1 hI).2
    have := pad_measure (c := c) hΘ hΘk hε hne0 μk I hIc Set.univ MeasurableSet.univ
    simp only [Set.mem_univ, and_true, Measure.restrict_univ] at this
    exact this

end D6

end P3f312ca3

namespace P8582bd15

/-- Derivative of the partial binomial sum. -/
theorem deriv_partial (N : ℕ) (e : ℝ) :
    ∀ k : ℕ, k + 1 ≤ N →
      HasDerivAt (fun x : ℝ => ∑ i ∈ Finset.range (k + 1),
          (N.choose i : ℝ) * x ^ i * (1 - x) ^ (N - i))
        (-((N.choose (k + 1) : ℝ) * ((1 - e) ^ (N - (k + 1)) * (((k + 1 : ℕ) : ℝ) * e ^ k)))) e := by
  intro k
  induction k with
  | zero =>
    intro hN
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    simp only [zero_add, Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, pow_zero,
      one_mul, Nat.sub_zero]
    have h : HasDerivAt (fun x : ℝ => (1 - x) ^ (m + 1))
        (((m + 1 : ℕ) : ℝ) * (1 - e) ^ (m + 1 - 1) * (-1)) e :=
      ((hasDerivAt_id' e).const_sub 1).pow (m + 1)
    refine h.congr_deriv ?_
    simp only [Nat.choose_one_right, Nat.add_sub_cancel]
    push_cast
    ring
  | succ k ih =>
    intro hN
    obtain ⟨m, rfl⟩ : ∃ m, N = k + 2 + m := ⟨N - (k + 2), by omega⟩
    have ih' := ih (by omega)
    have h1 : k + 2 + m - (k + 1) = m + 1 := by omega
    have h2 : k + 2 + m - (k + 1 + 1) = m := by omega
    rw [h1] at ih'
    rw [h2]
    have hc : ((k + 2 + m).choose (k + 1 + 1) : ℝ) * ((k + 1 + 1 : ℕ) : ℝ) =
        ((k + 2 + m).choose (k + 1) : ℝ) * ((m + 1 : ℕ) : ℝ) := by
      have := Nat.choose_succ_right_eq (k + 2 + m) (k + 1)
      rw [h1] at this
      exact_mod_cast this
    have hterm : HasDerivAt (fun x : ℝ => ((k + 2 + m).choose (k + 1) : ℝ) * x ^ (k + 1) *
        (1 - x) ^ (m + 1))
        (((k + 2 + m).choose (k + 1) : ℝ) * (((k + 1 : ℕ) : ℝ) * e ^ k) * (1 - e) ^ (m + 1) +
          ((k + 2 + m).choose (k + 1) : ℝ) * e ^ (k + 1) *
            (((m + 1 : ℕ) : ℝ) * (1 - e) ^ m * (-1))) e := by
      have a : HasDerivAt (fun x : ℝ => ((k + 2 + m).choose (k + 1) : ℝ) * x ^ (k + 1))
          (((k + 2 + m).choose (k + 1) : ℝ) * (((k + 1 : ℕ) : ℝ) * e ^ (k + 1 - 1))) e :=
        (hasDerivAt_pow (k + 1) e).const_mul _
      have b : HasDerivAt (fun x : ℝ => (1 - x) ^ (m + 1))
          (((m + 1 : ℕ) : ℝ) * (1 - e) ^ (m + 1 - 1) * (-1)) e :=
        ((hasDerivAt_id' e).const_sub 1).pow (m + 1)
      have c := a.mul b
      simp only [Nat.add_sub_cancel] at c
      exact c
    have hsum : HasDerivAt (fun x : ℝ => (∑ i ∈ Finset.range (k + 1),
          ((k + 2 + m).choose i : ℝ) * x ^ i * (1 - x) ^ (k + 2 + m - i)) +
          ((k + 2 + m).choose (k + 1) : ℝ) * x ^ (k + 1) * (1 - x) ^ (m + 1)) _ e :=
      ih'.add hterm
    have hfun : (fun x : ℝ => ∑ i ∈ Finset.range (k + 1 + 1),
          ((k + 2 + m).choose i : ℝ) * x ^ i * (1 - x) ^ (k + 2 + m - i)) =
        (fun x : ℝ => (∑ i ∈ Finset.range (k + 1),
          ((k + 2 + m).choose i : ℝ) * x ^ i * (1 - x) ^ (k + 2 + m - i)) +
          ((k + 2 + m).choose (k + 1) : ℝ) * x ^ (k + 1) * (1 - x) ^ (m + 1)) := by
      funext x
      rw [Finset.sum_range_succ, h1]
    rw [hfun]
    refine hsum.congr_deriv ?_
    push_cast at hc ⊢
    linear_combination ((1 - e) ^ m * e ^ (k + 1)) * hc

end P8582bd15

open MeasureTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace P3f312ca3

theorem choose_mul_integral_eq {d N : ℕ} (hd : 1 ≤ d) (hN : d ≤ N) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (N.choose d : ℝ) * ∫ α in ε..1, (1 - α) ^ (N - d) * ((d : ℝ) * α ^ (d - 1)) =
      ∑ i ∈ Finset.range d, (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set F : ℝ → ℝ := fun x => ∑ i ∈ Finset.range (k + 1),
    (N.choose i : ℝ) * x ^ i * (1 - x) ^ (N - i) with hF
  have hderiv : ∀ x ∈ Set.uIcc ε 1, HasDerivAt (fun x => -F x)
      ((N.choose (k + 1) : ℝ) * ((1 - x) ^ (N - (k + 1)) * (((k + 1 : ℕ) : ℝ) * x ^ k))) x := by
    intro x _
    have h := (P8582bd15.deriv_partial N x k hN).neg
    rw [neg_neg] at h
    exact h
  have hint : IntervalIntegrable (fun x : ℝ =>
      (N.choose (k + 1) : ℝ) * ((1 - x) ^ (N - (k + 1)) * (((k + 1 : ℕ) : ℝ) * x ^ k)))
      MeasureTheory.volume ε 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hF1 : F 1 = 0 := by
    simp only [hF]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    have : N - i ≠ 0 := by omega
    simp [this]
  show -F 1 - -F ε = F ε
  rw [hF1]
  ring


/-- The law with density `d v^(d-1)` on `[0,1]`. -/
noncomputable def betaMeas (d : ℕ) : Measure ℝ :=
  (volume.restrict (Set.Icc (0:ℝ) 1)).withDensity
    (fun v => ((Real.toNNReal ((d : ℝ) * v ^ (d - 1)) : ℝ≥0) : ℝ≥0∞))

theorem betaMeas_compl (d : ℕ) : betaMeas d (Set.Icc (0:ℝ) 1)ᶜ = 0 := by
  unfold betaMeas
  rw [withDensity_apply _ measurableSet_Icc.compl, Measure.restrict_restrict measurableSet_Icc.compl]
  simp

instance (d : ℕ) : IsFiniteMeasure (betaMeas d) := by
  unfold betaMeas
  refine isFiniteMeasure_withDensity (ne_of_lt (lt_of_le_of_lt
    (lintegral_mono_ae (g := fun _ => ((d : ℝ≥0) : ℝ≥0∞)) ?_) ?_))
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    have h1 : v ^ (d - 1) ≤ 1 := pow_le_one₀ hv.1 hv.2
    have h2 : Real.toNNReal ((d : ℝ) * v ^ (d - 1)) ≤ (d : ℝ≥0) := by
      rw [Real.toNNReal_le_iff_le_coe]
      push_cast
      nlinarith [pow_nonneg hv.1 (d - 1), (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
    exact_mod_cast h2
  · simp [lintegral_const, Real.volume_Icc]

theorem integral_betaMeas (d : ℕ) (g : ℝ → ℝ) :
    ∫ v, g v ∂(betaMeas d) = ∫ v in (0:ℝ)..1, (d : ℝ) * v ^ (d - 1) * g v := by
  unfold betaMeas
  rw [integral_withDensity_eq_integral_smul (by fun_prop)]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc (fun v hv => ?_)
  simp only [NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg d) (pow_nonneg hv.1 _))]

theorem betaMeas_moment {d : ℕ} (hd : 1 ≤ d) (j : ℕ) :
    ((j + d).choose d : ℝ) * ∫ v, (1 - v) ^ j ∂(betaMeas d) = 1 := by
  rw [integral_betaMeas]
  have h := choose_mul_integral_eq hd (N := j + d) (by omega) 0 le_rfl zero_le_one
  rw [show j + d - d = j by omega] at h
  have heq : (fun v : ℝ => (d : ℝ) * v ^ (d - 1) * (1 - v) ^ j) =
      fun v => (1 - v) ^ j * ((d : ℝ) * v ^ (d - 1)) := by
    funext v; ring
  rw [heq, h, Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    simp [zero_pow hi]
  · intro h0
    exact absurd (Finset.mem_range.2 (by omega)) h0

theorem integrable_of_supp {ν : Measure ℝ} [IsFiniteMeasure ν] (h : ν (Set.Icc (0:ℝ) 1)ᶜ = 0)
    {f : ℝ → ℝ} (hf : Continuous f) : Integrable f ν := by
  have hae : ∀ᵐ x ∂ν, x ∈ Set.Icc (0:ℝ) 1 := mem_ae_iff.2 h
  rw [← Measure.restrict_eq_self_of_ae_mem hae]
  exact hf.continuousOn.integrableOn_compact isCompact_Icc

/-- D3 (Hausdorff): a finite measure on `[0,1]` with the moments
`C(j+d,d) ∫ (1-v)^j = 1` is the law with density `d v^(d-1)`. -/
theorem hausdorff_eq {d : ℕ} (hd : 1 ≤ d) (m : Measure ℝ) [IsFiniteMeasure m]
    (hsupp : m (Set.Icc (0:ℝ) 1)ᶜ = 0)
    (hmom : ∀ j : ℕ, ((j + d).choose d : ℝ) * ∫ v, (1 - v) ^ j ∂m = 1) :
    m = betaMeas d := by
  have hμ := betaMeas_compl d
  have hmj : ∀ j : ℕ, ∫ v, (1 - v) ^ j ∂m = ∫ v, (1 - v) ^ j ∂(betaMeas d) := by
    intro j
    have hc : ((j + d).choose d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    exact mul_left_cancel₀ hc ((hmom j).trans (betaMeas_moment hd j).symm)
  have hpoly : ∀ p : Polynomial ℝ, ∫ v, p.eval v ∂m = ∫ v, p.eval v ∂(betaMeas d) := by
    intro p
    set q := p.comp (1 - Polynomial.X)
    have hpq : ∀ v, p.eval v = ∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * (1 - v) ^ j := by
      intro v
      have : p.eval v = q.eval (1 - v) := by simp [q, Polynomial.eval_comp]
      rw [this, Polynomial.eval_eq_sum_range]
    simp_rw [hpq]
    rw [integral_finsetSum _ (fun j _ => (integrable_of_supp hsupp (by fun_prop)).const_mul _),
      integral_finsetSum _ (fun j _ => (integrable_of_supp hμ (by fun_prop)).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_const_mul, hmj j]
  have hbc : ∀ f : ℝ →ᵇ ℝ, ∫ x, f x ∂m = ∫ x, f x ∂(betaMeas d) := by
    intro f
    refine eq_of_forall_dist_le fun η hη => ?_
    set C := (m Set.univ).toReal + ((betaMeas d) Set.univ).toReal + 1 with hCdef
    have hC : 0 < C := by positivity
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f f.continuous.continuousOn
      (η / C) (div_pos hη hC)
    have key : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν], ν (Set.Icc (0:ℝ) 1)ᶜ = 0 →
        |∫ x, f x ∂ν - ∫ x, p.eval x ∂ν| ≤ η / C * (ν Set.univ).toReal := by
      intro ν _ hν
      have hae : ∀ᵐ x ∂ν, x ∈ Set.Icc (0:ℝ) 1 := mem_ae_iff.2 hν
      rw [← integral_sub (integrable_of_supp hν f.continuous)
        (integrable_of_supp hν (Polynomial.continuous p)), ← Real.norm_eq_abs]
      have := norm_integral_le_of_norm_le_const (μ := ν) (C := η / C)
        (f := fun x => f x - p.eval x) (by
          filter_upwards [hae] with x hx
          rw [Real.norm_eq_abs, abs_sub_comm]; exact (hp x hx).le)
      simpa [Measure.real] using this
    have k1 := key m hsupp
    have k2 := key (betaMeas d) hμ
    rw [hpoly p] at k1
    rw [Real.dist_eq]
    have hm0 : 0 ≤ (m Set.univ).toReal := ENNReal.toReal_nonneg
    have hb0 : 0 ≤ ((betaMeas d) Set.univ).toReal := ENNReal.toReal_nonneg
    have hsum : η / C * (m Set.univ).toReal + η / C * ((betaMeas d) Set.univ).toReal ≤ η := by
      rw [← mul_add, div_mul_eq_mul_div, div_le_iff₀ hC]
      nlinarith
    calc |∫ x, f x ∂m - ∫ x, f x ∂(betaMeas d)|
        = |(∫ x, f x ∂m - ∫ x, p.eval x ∂(betaMeas d)) -
            (∫ x, f x ∂(betaMeas d) - ∫ x, p.eval x ∂(betaMeas d))| := by ring_nf
      _ ≤ |∫ x, f x ∂m - ∫ x, p.eval x ∂(betaMeas d)| +
            |∫ x, f x ∂(betaMeas d) - ∫ x, p.eval x ∂(betaMeas d)| := abs_sub _ _
      _ ≤ η := by linarith
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure hbc

end P3f312ca3

namespace P3f312ca3

section D6b

variable {d L : ℕ} {c : EuclideanSpace ℝ (Fin d)} {Θ : Set (EuclideanSpace ℝ (Fin d))}
  {Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))} {ε : ℝ}

/-- Probability that a fresh heated point is good for the sample `a`. -/
noncomputable def qf (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) (μk : Measure (Fin L))
    (a : Fin d → Fin L × ℝ) : ℝ :=
  (heatMeas μk {x | GoodL c Θ Θk ε a x}).toReal

theorem measurable_qf (hΘ : Convex ℝ Θ) (hΘk : ∀ k, Convex ℝ (Θk k)) (hε : 0 < ε)
    (hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θk k).Nonempty)
    (μk : Measure (Fin L)) [IsProbabilityMeasure μk] : Measurable (qf c Θ Θk ε μk) := by
  show Measurable fun a => (heatMeas μk (Prod.mk a ⁻¹'
    {p : (Fin d → Fin L × ℝ) × (Fin L × ℝ) | GoodL c Θ Θk ε p.1 p.2})).toReal
  exact (measurable_measure_prodMk_left (measurableSet_goodL (c := c) hΘ hΘk hε hne0 d)).ennreal_toReal

theorem qf_mem (μk : Measure (Fin L)) [IsProbabilityMeasure μk] (a : Fin d → Fin L × ℝ) :
    qf c Θ Θk ε μk a ∈ Set.Icc (0:ℝ) 1 :=
  ⟨ENNReal.toReal_nonneg, by unfold qf; simpa using ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one⟩

theorem lintegral_pow_eq_ofReal (hΘ : Convex ℝ Θ) (hΘk : ∀ k, Convex ℝ (Θk k)) (hε : 0 < ε)
    (hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θk k).Nonempty)
    (μk : Measure (Fin L)) [IsProbabilityMeasure μk] (j : ℕ) :
    ∫⁻ a, heatMeas μk {x | GoodL c Θ Θk ε a x} ^ j ∂(Measure.pi fun _ : Fin d => heatMeas μk) =
      ENNReal.ofReal (∫ a, qf c Θ Θk ε μk a ^ j ∂(Measure.pi fun _ : Fin d => heatMeas μk)) := by
  have hm := measurable_qf (c := c) hΘ hΘk hε hne0 μk
  rw [ofReal_integral_eq_lintegral_ofReal]
  · refine lintegral_congr fun a => ?_
    rw [qf, ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · refine (integrable_const (1:ℝ)).mono' (hm.pow_const j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => ?_)
    have h := qf_mem (c := c) (Θ := Θ) (Θk := Θk) (ε := ε) μk a
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h.1 _)]
    exact pow_le_one₀ h.1 h.2
  · exact Filter.Eventually.of_forall fun a => pow_nonneg (qf_mem μk a).1 _

theorem moments_qf (hΘ : Convex ℝ Θ) (hΘk : ∀ k, Convex ℝ (Θk k)) (hε : 0 < ε)
    (hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θk k).Nonempty)
    (μk : Measure (Fin L)) [IsProbabilityMeasure μk] (j : ℕ) :
    ((j + d).choose d : ℝ) *
      ∫ a, qf c Θ Θk ε μk a ^ j ∂(Measure.pi fun _ : Fin d => heatMeas μk) = 1 := by
  have h := choose_mul_phi (c := c) hΘ hΘk hε hne0 μk (M := j + d) (by omega)
  rw [Nat.add_sub_cancel, lintegral_pow_eq_ofReal hΘ hΘk hε hne0] at h
  have hnn : 0 ≤ ∫ a, qf c Θ Θk ε μk a ^ j ∂(Measure.pi fun _ : Fin d => heatMeas μk) :=
    integral_nonneg fun a => pow_nonneg (qf_mem μk a).1 _
  have := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn] at this
  simpa using this

/-- The law of the conflict probability `1 - qf`. -/
noncomputable def mOf (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))) (ε : ℝ) (μk : Measure (Fin L)) : Measure ℝ :=
  (Measure.pi fun _ : Fin d => heatMeas μk).map fun a => 1 - qf c Θ Θk ε μk a

theorem mOf_eq_beta (hd : 1 ≤ d) (hΘ : Convex ℝ Θ) (hΘk : ∀ k, Convex ℝ (Θk k)) (hε : 0 < ε)
    (hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θk k).Nonempty)
    (μk : Measure (Fin L)) [IsProbabilityMeasure μk] :
    mOf c Θ Θk ε μk = betaMeas d := by
  have hm : Measurable fun a => 1 - qf c Θ Θk ε μk a :=
    measurable_const.sub (measurable_qf hΘ hΘk hε hne0 μk)
  have : IsProbabilityMeasure (mOf c Θ Θk ε μk) := Measure.isProbabilityMeasure_map hm.aemeasurable
  apply hausdorff_eq hd
  · unfold mOf
    rw [Measure.map_apply hm measurableSet_Icc.compl]
    have : (fun a => 1 - qf c Θ Θk ε μk a) ⁻¹' (Set.Icc (0:ℝ) 1)ᶜ = ∅ := by
      ext a
      have h := qf_mem (c := c) (Θ := Θ) (Θk := Θk) (ε := ε) μk a
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, Set.mem_empty_iff_false,
        iff_false, not_not]
      constructor <;> linarith [h.1, h.2]
    rw [this, measure_empty]
  · intro j
    unfold mOf
    rw [integral_map hm.aemeasurable
      (by fun_prop : Continuous fun v : ℝ => (1 - v) ^ j).aestronglyMeasurable]
    simp only [sub_sub_cancel]
    exact moments_qf hΘ hΘk hε hne0 μk j

/-- Heated finite theorem: the violation tail of the heated solution is at most the binomial
tail. -/
theorem heated_tail (hd : 1 ≤ d) (hΘ : Convex ℝ Θ) (hΘk : ∀ k, Convex ℝ (Θk k)) (hε : 0 < ε)
    (hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θk k).Nonempty)
    (μk : Measure (Fin L)) [IsProbabilityMeasure μk] {N : ℕ} (hN : d ≤ N) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Measure.pi (fun _ : Fin N => heatMeas μk)
      {ω | t < (heatMeas μk {x | solH c Θ Θk ε ω Finset.univ ∉ Cset Θk ε x}).toReal} ≤
      ENNReal.ofReal (∑ i ∈ Finset.range d, (N.choose i : ℝ) * t ^ i * (1 - t) ^ (N - i)) := by
  set Pm := Measure.pi (fun _ : Fin N => heatMeas μk) with hPm
  set Pd := Measure.pi (fun _ : Fin d => heatMeas μk) with hPd
  set E : Set (Fin N → Fin L × ℝ) :=
    {ω | t < (heatMeas μk {x | solH c Θ Θk ε ω Finset.univ ∉ Cset Θk ε x}).toReal} with hE
  set s := (Finset.univ : Finset (Fin N)).powersetCard d with hs
  set f : Finset (Fin N) → Set (Fin N → Fin L × ℝ) := fun I =>
    {ω | IsPad (sol := solH c Θ Θk ε ω) d (fun i => (ω i).2) Finset.univ I} ∩ E with hf
  set R : Set (Fin d → Fin L × ℝ) := {a | t < 1 - qf c Θ Θk ε μk a} with hRdef
  have hm : Measurable fun a => 1 - qf c Θ Θk ε μk a :=
    measurable_const.sub (measurable_qf hΘ hΘk hε hne0 μk)
  have hR : MeasurableSet R := measurableSet_lt measurable_const hm
  have hcov : ∀ᵐ ω ∂Pm, ω ∈ E → ω ∈ ⋃ I ∈ s, f I := by
    filter_upwards [ae_nondeg (c := c) hΘ hΘk hε hne0 μk N, ae_injOn_label μk N] with ω hnd hinj hEω
    have hsp := heatSpec c hΘ hΘk hε ω (fun S => hne_of hne0 ω S)
    obtain ⟨I0, hI0⟩ := exists_isPad (sol := solH c Θ Θk ε ω) (d := d) (fun i => (ω i).2) hinj
      (by rw [Finset.card_univ, Fintype.card_fin]; exact hN)
      (fun B hB => heat_basis_card hΘ hΘk hε hsp Finset.univ B hB)
    have hI0c : I0.card = d := by obtain ⟨_, _, _, _, hc, _⟩ := hI0; exact hc
    exact Set.mem_iUnion₂.2 ⟨I0, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hI0c⟩, hI0, hEω⟩
  have hterm : ∀ I ∈ s, Pm (f I) ≤
      ∫⁻ a in R, heatMeas μk {x | GoodL c Θ Θk ε a x} ^ (N - d) ∂Pd := by
    intro I hI
    have hIc := (Finset.mem_powersetCard.1 hI).2
    rw [← pad_measure (c := c) hΘ hΘk hε hne0 μk I hIc R hR]
    refine measure_mono fun ω hω => ⟨hω.1, ?_⟩
    obtain ⟨hpad, hEω⟩ := hω
    have hlp : LPType (solH c Θ Θk ε ω) (fun θ i => θ ∈ Cset Θk ε (ω i)) :=
      heat_lpType (heatSpec c hΘ hΘk hε ω (fun S => hne_of hne0 ω S))
    have hsolI : solH c Θ Θk ε ω I = solH c Θ Θk ε ω Finset.univ := by
      obtain ⟨B, hB, hBI, hIS, -, -⟩ := hpad
      exact (hlp.sandwich hBI hIS hB.2.1).trans hB.2.1
    have hsol : solH c Θ Θk ε (ω ∘ ιOf I hIc) Finset.univ = solH c Θ Θk ε ω Finset.univ := by
      rw [← solH_map, map_ιOf, hsolI]
    have hG := measurableSet_goodL (c := c) hΘ hΘk hε hne0 d
    have hGa : MeasurableSet {x | GoodL c Θ Θk ε (ω ∘ ιOf I hIc) x} := measurable_prodMk_left hG
    have hsub : {x | solH c Θ Θk ε ω Finset.univ ∉ Cset Θk ε x} ⊆
        {x | GoodL c Θ Θk ε (ω ∘ ιOf I hIc) x}ᶜ := by
      intro x hx hgood
      apply hx
      rw [← hsol]
      exact hgood.1
    have hle : (heatMeas μk {x | solH c Θ Θk ε ω Finset.univ ∉ Cset Θk ε x}).toReal ≤
        1 - qf c Θ Θk ε μk (ω ∘ ιOf I hIc) := by
      have h1 := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (μ := heatMeas μk) hsub)
      rw [prob_compl_eq_one_sub hGa, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
        ENNReal.toReal_one] at h1
      exact h1
    exact lt_of_lt_of_le hEω hle
  have hint : ∫⁻ a in R, heatMeas μk {x | GoodL c Θ Θk ε a x} ^ (N - d) ∂Pd =
      ENNReal.ofReal (∫ v in t..1, (1 - v) ^ (N - d) * ((d : ℝ) * v ^ (d - 1))) := by
    set g : ℝ → ℝ≥0∞ := (Set.Ioi t).indicator fun v => ENNReal.ofReal ((1 - v) ^ (N - d)) with hg
    have hgm : Measurable g :=
      (Measurable.ennreal_ofReal (by fun_prop)).indicator measurableSet_Ioi
    have hae01 : ∀ᵐ v ∂(betaMeas d), v ∈ Set.Icc (0:ℝ) 1 := mem_ae_iff.2 (betaMeas_compl d)
    calc ∫⁻ a in R, heatMeas μk {x | GoodL c Θ Θk ε a x} ^ (N - d) ∂Pd
        = ∫⁻ a, g (1 - qf c Θ Θk ε μk a) ∂Pd := by
          rw [← lintegral_indicator hR]
          refine lintegral_congr fun a => ?_
          by_cases ha : a ∈ R
          · have ha' : (1 - qf c Θ Θk ε μk a) ∈ Set.Ioi t := ha
            rw [Set.indicator_of_mem ha, hg, Set.indicator_of_mem ha', sub_sub_cancel, qf,
              ENNReal.ofReal_pow ENNReal.toReal_nonneg,
              ENNReal.ofReal_toReal (measure_ne_top _ _)]
          · have ha' : (1 - qf c Θ Θk ε μk a) ∉ Set.Ioi t := ha
            rw [Set.indicator_of_notMem ha, hg, Set.indicator_of_notMem ha']
      _ = ∫⁻ v, g v ∂(mOf c Θ Θk ε μk) := (lintegral_map hgm hm).symm
      _ = ∫⁻ v, g v ∂(betaMeas d) := by rw [mOf_eq_beta hd hΘ hΘk hε hne0 μk]
      _ = ENNReal.ofReal (∫ v, (Set.Ioi t).indicator (fun v => (1 - v) ^ (N - d)) v
            ∂(betaMeas d)) := by
          rw [ofReal_integral_eq_lintegral_ofReal]
          · refine lintegral_congr fun v => ?_
            by_cases hv : v ∈ Set.Ioi t
            · rw [hg, Set.indicator_of_mem hv, Set.indicator_of_mem hv]
            · rw [hg, Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, ENNReal.ofReal_zero]
          · exact (integrable_of_supp (betaMeas_compl d)
              (by fun_prop : Continuous fun v : ℝ => (1 - v) ^ (N - d))).indicator measurableSet_Ioi
          · filter_upwards [hae01] with v hv
            by_cases hvt : v ∈ Set.Ioi t
            · rw [Set.indicator_of_mem hvt]
              exact pow_nonneg (by linarith [hv.2]) _
            · rw [Set.indicator_of_notMem hvt]; simp
      _ = ENNReal.ofReal (∫ v in t..1, (1 - v) ^ (N - d) * ((d : ℝ) * v ^ (d - 1))) := by
          congr 1
          rw [integral_betaMeas, intervalIntegral.integral_of_le zero_le_one,
            intervalIntegral.integral_of_le ht1]
          have hfun : (fun v : ℝ => (d : ℝ) * v ^ (d - 1) *
              (Set.Ioi t).indicator (fun v => (1 - v) ^ (N - d)) v) =
              (Set.Ioi t).indicator (fun v => (1 - v) ^ (N - d) * ((d : ℝ) * v ^ (d - 1))) := by
            funext v
            by_cases hv : v ∈ Set.Ioi t
            · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]; ring
            · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, mul_zero]
          rw [hfun, setIntegral_indicator measurableSet_Ioi]
          have hset : Set.Ioc (0:ℝ) 1 ∩ Set.Ioi t = Set.Ioc t 1 := by
            ext v
            simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
            constructor
            · rintro ⟨⟨_, h1⟩, ht⟩; exact ⟨ht, h1⟩
            · rintro ⟨ht', h1⟩; exact ⟨⟨by linarith, h1⟩, ht'⟩
          rw [hset]
  calc Pm E ≤ Pm (⋃ I ∈ s, f I) := measure_mono_ae hcov
    _ ≤ ∑ I ∈ s, Pm (f I) := measure_biUnion_finset_le s f
    _ ≤ ∑ I ∈ s, ∫⁻ a in R, heatMeas μk {x | GoodL c Θ Θk ε a x} ^ (N - d) ∂Pd :=
        Finset.sum_le_sum hterm
    _ = (N.choose d : ℝ≥0∞) *
          ENNReal.ofReal (∫ v in t..1, (1 - v) ^ (N - d) * ((d : ℝ) * v ^ (d - 1))) := by
        rw [Finset.sum_const, hs, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, hint]
    _ = ENNReal.ofReal (∑ i ∈ Finset.range d, (N.choose i : ℝ) * t ^ i * (1 - t) ^ (N - i)) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          choose_mul_integral_eq hd hN t ht0 ht1]

end D6b

section F2

open Filter Topology

variable {d L : ℕ} {c : EuclideanSpace ℝ (Fin d)} {Θ : Set (EuclideanSpace ℝ (Fin d))}
  {Θk : Fin L → Set (EuclideanSpace ℝ (Fin d))}

theorem eventually_lt_infEDist {θ0 : EuclideanSpace ℝ (Fin d)} {x : ℕ → EuclideanSpace ℝ (Fin d)}
    (hx : Tendsto x atTop (𝓝 θ0)) {A : Set (EuclideanSpace ℝ (Fin d))} (hA : IsClosed A)
    (h0 : θ0 ∉ A) {εn : ℕ → ℝ} (hε0 : Tendsto εn atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ENNReal.ofReal (2 * εn n) < Metric.infEDist (x n) A := by
  have hpos : 0 < Metric.infEDist θ0 A := by
    rw [pos_iff_ne_zero]
    intro h
    apply h0
    rw [← hA.closure_eq, Metric.mem_closure_iff_infEDist_zero]
    exact h
  have h1 : Tendsto (fun n => Metric.infEDist (x n) A) atTop (𝓝 (Metric.infEDist θ0 A)) :=
    (Metric.continuous_infEDist.tendsto θ0).comp hx
  have h2 : Tendsto (fun n => ENNReal.ofReal (2 * εn n)) atTop (𝓝 0) := by
    have h2' : Tendsto (fun n => 2 * εn n) atTop (𝓝 0) := by
      simpa using hε0.const_mul 2
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h2'
    rw [ENNReal.ofReal_zero] at this
    exact this
  exact h2.eventually_lt h1 hpos

/-- F2: the finite (`Δ = Fin L`) case of the bound, for any law `μk` on `Fin L`. -/
theorem finite_tail (hd : 1 ≤ d) (hΘ : Convex ℝ Θ) (hΘc : IsClosed Θ)
    (hΘk : ∀ k, Convex ℝ (Θk k)) (hΘkc : ∀ k, IsClosed (Θk k))
    (hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θk k).Nonempty)
    (μk : Measure (Fin L)) [IsProbabilityMeasure μk] {N : ℕ} (hN : d ≤ N)
    (θs : (Fin N → Fin L) → EuclideanSpace ℝ (Fin d))
    (hθs : ∀ κ, θs κ ∈ Θ ∩ ⋂ i, Θk (κ i))
    (huniq : ∀ κ, ∀ y ∈ Θ ∩ ⋂ i, Θk (κ i), inner ℝ c y ≤ inner ℝ c (θs κ) → y = θs κ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Measure.pi (fun _ : Fin N => μk) {κ | t < (μk {k | θs κ ∉ Θk k}).toReal} ≤
      ENNReal.ofReal (∑ i ∈ Finset.range d, (N.choose i : ℝ) * t ^ i * (1 - t) ^ (N - i)) := by
  classical
  set εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεn
  have hεpos : ∀ n, 0 < εn n := fun n => by simp only [hεn]; positivity
  have hε0 : Tendsto εn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set Pm := Measure.pi fun _ : Fin N => heatMeas μk with hPm
  set En : ℕ → Set (Fin N → Fin L × ℝ) := fun n =>
    {ω | t < (heatMeas μk {x | solH c Θ Θk (εn n) ω Finset.univ ∉ Cset Θk (εn n) x}).toReal}
    with hEn
  set Fn : ℕ → Set (Fin N → Fin L × ℝ) := fun n => ⋂ m, ⋂ (_ : n ≤ m), En m with hFn
  have hmono : Monotone Fn := fun a b hab ω hω =>
    Set.mem_iInter₂.2 fun m hm => Set.mem_iInter₂.1 hω m (hab.trans hm)
  have hmp : MeasurePreserving (fun (ω : Fin N → Fin L × ℝ) (i : Fin N) => (ω i).1) Pm
      (Measure.pi fun _ : Fin N => μk) :=
    measurePreserving_pi _ _ fun _ => (by unfold heatMeas; exact measurePreserving_fst)
  set E : Set (Fin N → Fin L) := {κ | t < (μk {k | θs κ ∉ Θk k}).toReal} with hE
  rw [← hmp.measure_preimage (Set.to_countable E).measurableSet.nullMeasurableSet]
  have hU : ∀ᵐ ω ∂Pm, ∀ i, (ω i).2 ∈ Set.Icc (0:ℝ) 1 := by
    rw [ae_all_iff]
    intro i
    have hev := measurePreserving_eval (fun _ : Fin N => heatMeas μk) i
    rw [ae_iff]
    have : {ω : Fin N → Fin L × ℝ | ¬ (ω i).2 ∈ Set.Icc (0:ℝ) 1} =
        Function.eval i ⁻¹' (Set.univ ×ˢ (Set.Icc (0:ℝ) 1)ᶜ) := by
      ext ω; simp
    rw [this, hev.measure_preimage
      (MeasurableSet.univ.prod measurableSet_Icc.compl).nullMeasurableSet]
    unfold heatMeas
    rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Icc.compl]
    simp
  have hcov : ∀ᵐ ω ∂Pm, ω ∈ (fun (ω : Fin N → Fin L × ℝ) (i : Fin N) => (ω i).1) ⁻¹' E →
      ω ∈ ⋃ n, Fn n := by
    filter_upwards [hU] with ω hω hEω
    set κ : Fin N → Fin L := fun i => (ω i).1 with hκ
    set sol : ℕ → EuclideanSpace ℝ (Fin d) := fun n => solH c Θ Θk (εn n) ω Finset.univ
      with hsol
    have hspec : ∀ n, sol n ∈ Feps Θ Θk (εn n) ω Finset.univ ∧
        ∀ y ∈ Feps Θ Θk (εn n) ω Finset.univ, fobj c (εn n) (sol n) ≤ fobj c (εn n) y := by
      intro n
      obtain ⟨θ0, h0⟩ := hne_of hne0 ω Finset.univ
      exact solOf_spec c (hεpos n) (isClosed_Feps Θ Θk _ ω _)
        ⟨θ0, ball_subset_Feps (hεpos n).le ω Finset.univ h0 (Metric.mem_ball_self (hεpos n))⟩
    have htend : Tendsto sol atTop (𝓝 (θs κ)) := by
      refine tendsto_heated c (F := Θ ∩ ⋂ i, Θk (κ i))
        (Fn := fun n => Feps Θ Θk (εn n) ω Finset.univ) hεpos hε0 ?_
        (fun n => convex_Feps hΘ hΘk _ ω _) ?_ (hθs κ) (huniq κ) sol hspec
      · intro n y hy
        rw [mem_Feps_iff]
        exact ⟨Metric.self_subset_cthickening _ hy.1,
          fun i _ => Metric.self_subset_cthickening _ (Set.mem_iInter.1 hy.2 i)⟩
      · intro φ hφ y y0 hy hyt
        refine ⟨mem_of_tendsto_cthickening hΘc (hε0.comp hφ.tendsto_atTop)
          (fun k => (mem_Feps_iff.1 (hy k)).1) hyt, Set.mem_iInter.2 fun i => ?_⟩
        refine mem_of_tendsto_cthickening (hΘkc _) (r := fun k => rad (εn (φ k)) (ω i)) ?_
          (fun k => (mem_Feps_iff.1 (hy k)).2 i (Finset.mem_univ i)) hyt
        have := (hε0.comp hφ.tendsto_atTop).mul_const (1 + |(ω i).2|)
        simpa [rad] using this
    have hev : ∀ᶠ n in atTop, ∀ k : Fin L, θs κ ∉ Θk k →
        ENNReal.ofReal (2 * εn n) < Metric.infEDist (sol n) (Θk k) := by
      rw [Filter.eventually_all]
      intro k
      by_cases hk : θs κ ∈ Θk k
      · exact Filter.Eventually.of_forall fun n h => absurd hk h
      · filter_upwards [eventually_lt_infEDist htend (hΘkc k) hk hε0] with n hn _ using hn
    obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.1 hev
    refine Set.mem_iUnion.2 ⟨n0, Set.mem_iInter₂.2 fun m hm => ?_⟩
    have hsub : {k | θs κ ∉ Θk k} ×ˢ Set.Icc (0:ℝ) 1 ⊆ {x | sol m ∉ Cset Θk (εn m) x} := by
      rintro ⟨k, u⟩ ⟨hk, hu⟩ hmem
      have h1 := hn0 m hm k hk
      have h2 : Metric.infEDist (sol m) (Θk k) ≤ ENNReal.ofReal (rad (εn m) (k, u)) :=
        Metric.mem_cthickening_iff.1 hmem
      have h3 : rad (εn m) (k, u) ≤ 2 * εn m := by
        unfold rad
        have := hεpos m
        have hu1 : |u| ≤ 1 := abs_le.2 ⟨by linarith [hu.1], hu.2⟩
        simp only
        nlinarith
      exact absurd (h2.trans (ENNReal.ofReal_le_ofReal h3)) (not_le.2 h1)
    have hmeasK : heatMeas μk ({k | θs κ ∉ Θk k} ×ˢ Set.Icc (0:ℝ) 1) = μk {k | θs κ ∉ Θk k} := by
      unfold heatMeas
      rw [Measure.prod_prod]
      simp [Real.volume_Icc]
    show t < (heatMeas μk {x | solH c Θ Θk (εn m) ω Finset.univ ∉ Cset Θk (εn m) x}).toReal
    calc t < (μk {k | θs κ ∉ Θk k}).toReal := hEω
      _ = (heatMeas μk ({k | θs κ ∉ Θk k} ×ˢ Set.Icc (0:ℝ) 1)).toReal := by rw [hmeasK]
      _ ≤ _ := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  calc Pm ((fun (ω : Fin N → Fin L × ℝ) (i : Fin N) => (ω i).1) ⁻¹' E) ≤ Pm (⋃ n, Fn n) :=
        measure_mono_ae hcov
    _ = ⨆ n, Pm (Fn n) := hmono.measure_iUnion
    _ ≤ _ := iSup_le fun n => (measure_mono (Set.iInter₂_subset n le_rfl)).trans
        (heated_tail hd hΘ hΘk (hεpos n) hne0 μk hN t ht0 ht1)

end F2

open ProbabilityTheory


open MeasureTheory ProbabilityTheory

section D8a

variable {Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ) [IsProbabilityMeasure P]

/-- Splitting `Fin L → Δ` into the coordinates hit by an injection `κ` and the rest. -/
theorem pi_split {L N : ℕ} (κ : Fin N ↪ Fin L) :
    MeasurePreserving
      (fun y : Fin L → Δ => ((fun i => y (κ i)),
        (fun j : {x // x ∉ Finset.univ.map κ} => y j)))
      (Measure.pi fun _ : Fin L => P)
      ((Measure.pi fun _ : Fin N => P).prod
        (Measure.pi fun _ : {x // x ∉ Finset.univ.map κ} => P)) := by
  classical
  set I := Finset.univ.map κ with hI
  set e : Fin N ≃ {x // x ∈ I} := Equiv.ofBijective
    (fun i => ⟨κ i, Finset.mem_map_of_mem _ (Finset.mem_univ i)⟩)
    ⟨fun a b h => κ.injective (congrArg Subtype.val h), fun x => by
      obtain ⟨i, -, hi⟩ := Finset.mem_map.1 x.2
      exact ⟨i, Subtype.ext hi⟩⟩ with he
  set σ : Fin N ⊕ {x // x ∉ I} ≃ Fin L :=
    (Equiv.sumCongr e (Equiv.refl {x // x ∉ I})).trans (Equiv.sumCompl (· ∈ I)) with hσ
  have h1 := MeasurePreserving.symm _ (measurePreserving_piCongrLeft (fun _ : Fin L => P) σ)
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin N ⊕ {x // x ∉ I} => Δ)
    (fun _ : Fin N ⊕ {x // x ∉ I} => P)
  have h3 := h2.comp h1
  convert h3 using 1
  funext y
  simp only [Function.comp_apply, MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
    Equiv.coe_fn_mk]
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · show y (κ i) = (MeasurableEquiv.piCongrLeft (fun _ : Fin L => Δ) σ).symm y (Sum.inl i)
    simp [MeasurableEquiv.piCongrLeft, hσ, he]
    all_goals rfl
  · show y j = (MeasurableEquiv.piCongrLeft (fun _ : Fin L => Δ) σ).symm y (Sum.inr j)
    simp [MeasurableEquiv.piCongrLeft, hσ]

/-- Chebyshev: few sample points fall in `A` only with small probability. -/
theorem count_lower_tail {ι : Type*} [Fintype ι] (A : Set Δ) (hA : MeasurableSet A)
    (s D : ℝ) (hD : 0 < D) (hsD : s + D ≤ (Fintype.card ι : ℝ) * (P A).toReal) :
    Measure.pi (fun _ : ι => P)
      {z | (∑ j, A.indicator (fun _ => (1:ℝ)) (z j)) ≤ s} ≤
      ENNReal.ofReal (Fintype.card ι / D ^ 2) := by
  classical
  set μ := Measure.pi fun _ : ι => P with hμ
  set X : ι → (ι → Δ) → ℝ := fun j z => A.indicator (fun _ => (1:ℝ)) (z j) with hX
  have hXm : ∀ j, Measurable (X j) := fun j =>
    (measurable_const.indicator hA).comp (measurable_pi_apply j)
  have hbd : ∀ j z, ‖X j z‖ ≤ 1 := by
    intro j z
    simp only [hX, Set.indicator]
    split_ifs <;> simp
  have hL2 : ∀ j, MemLp (X j) 2 μ := fun j =>
    MemLp.of_bound (hXm j).aestronglyMeasurable 1 (Filter.Eventually.of_forall (hbd j))
  have hS : (fun z => ∑ j, X j z) = ∑ j, X j := by
    funext z; simp [Finset.sum_apply]
  have hSL2 : MemLp (∑ j, X j) 2 μ := memLp_finsetSum' _ fun j _ => hL2 j
  have hind : iIndepFun (fun j z => A.indicator (fun _ => (1:ℝ)) (z j)) μ :=
    iIndepFun_pi (X := fun _ : ι => A.indicator (fun _ => (1:ℝ)))
      (fun _ => (measurable_const.indicator hA).aemeasurable)
  have hvar : variance (∑ j, X j) μ ≤ Fintype.card ι := by
    rw [IndepFun.variance_sum (fun j _ => hL2 j)
      (fun i _ j _ hij => hind.indepFun hij)]
    calc ∑ j, variance (X j) μ ≤ ∑ _j : ι, (1:ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine (variance_le_expectation_sq (hXm j).aestronglyMeasurable).trans ?_
          have h := norm_integral_le_of_norm_le_const (μ := μ) (C := 1)
            (f := X j ^ 2) (Filter.Eventually.of_forall fun z => by
              have := hbd j z
              simp only [Pi.pow_apply, norm_pow]
              exact pow_le_one₀ (norm_nonneg _) this)
          refine (le_abs_self _).trans ?_
          rw [← Real.norm_eq_abs]
          simpa using h
      _ = Fintype.card ι := by simp
  have hmean : μ[∑ j, X j] = (Fintype.card ι : ℝ) * (P A).toReal := by
    simp only [Finset.sum_apply]
    rw [integral_finset_sum _ fun j _ => (hL2 j).integrable one_le_two]
    have : ∀ j, ∫ z, X j z ∂μ = (P A).toReal := by
      intro j
      have hev := measurePreserving_eval (fun _ : ι => P) j
      have := integral_map (μ := μ) hev.measurable.aemeasurable
        (f := A.indicator (fun _ => (1:ℝ)))
        ((measurable_const.indicator hA).aestronglyMeasurable)
      rw [hev.map_eq] at this
      rw [show (fun z => X j z) = fun z => A.indicator (fun _ => (1:ℝ)) (Function.eval j z)
        from rfl, ← this, integral_indicator_const _ hA]
      simp [measureReal_def]
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsub : {z | (∑ j, A.indicator (fun _ => (1:ℝ)) (z j)) ≤ s} ⊆
      {z | D ≤ |(∑ j, X j) z - μ[∑ j, X j]|} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    rw [hmean, Finset.sum_apply]
    rw [abs_sub_comm]
    refine le_trans ?_ (le_abs_self _)
    simp only [hX]
    linarith
  calc μ {z | (∑ j, A.indicator (fun _ => (1:ℝ)) (z j)) ≤ s}
      ≤ μ {z | D ≤ |(∑ j, X j) z - μ[∑ j, X j]|} := measure_mono hsub
    _ ≤ ENNReal.ofReal (variance (∑ j, X j) μ / D ^ 2) := meas_ge_le_variance_div_sq hSL2 hD
    _ ≤ ENNReal.ofReal (Fintype.card ι / D ^ 2) :=
        ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hvar (sq_nonneg D))

end D8a


section D8

open Filter Topology

/-- The uniform law on `Fin L`. -/
noncomputable def unifL (L : ℕ) : Measure (Fin L) :=
  ∑ l : Fin L, ((L : ℝ≥0∞)⁻¹) • Measure.dirac l

theorem unifL_apply (L : ℕ) (S : Set (Fin L)) :
    unifL L S = ∑ l : Fin L, S.indicator (fun _ => (L : ℝ≥0∞)⁻¹) l := by
  simp only [unifL, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Measure.dirac_apply' _ (Set.toFinite S).measurableSet]
  by_cases h : l ∈ S <;> simp [Set.indicator, h]

theorem unifL_prob {L : ℕ} (hL : 0 < L) : IsProbabilityMeasure (unifL L) := by
  refine ⟨?_⟩
  rw [unifL_apply]
  simp only [Set.indicator_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hL.ne') (ENNReal.natCast_ne_top L)

theorem unifL_toReal (L : ℕ) (S : Set (Fin L)) :
    (unifL L S).toReal = ∑ l : Fin L, S.indicator (fun _ => (L : ℝ)⁻¹) l := by
  rw [unifL_apply, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : l ∈ S <;> simp [Set.indicator, h, ENNReal.toReal_inv]
  · intro l _
    have hL : (L : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Fin.pos l).ne'
    by_cases h : l ∈ S <;> simp [Set.indicator, h, hL]

theorem unifL_singleton {L : ℕ} (a : Fin L) : unifL L {a} = (L : ℝ≥0∞)⁻¹ := by
  rw [unifL_apply]
  simp [Set.indicator_apply]

theorem binSum_nonneg (d N : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ ∑ i ∈ Finset.range d, (N.choose i : ℝ) * t ^ i * (1 - t) ^ (N - i) :=
  Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht0 _))
    (pow_nonneg (by linarith) _)

variable {d : ℕ}

/-- D8: the general bound at `ε - η`, by reduction to the empirical finite problem. -/
theorem general_tail_eta (hd : 1 ≤ d) {Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ)
    [IsProbabilityMeasure P] (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d))) (hΘ : Convex ℝ Θ) (hΘc : IsClosed Θ)
    (hΘδ : ∀ δ, Convex ℝ (Θδ δ)) (hΘδc : ∀ δ, IsClosed (Θδ δ))
    (hne : ∀ (m : ℕ) (ω : Fin m → Δ), (Θ ∩ ⋂ i, Θδ (ω i)).Nonempty)
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    {N : ℕ} (hN : d ≤ N) (θstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθm : Measurable θstar) (hθs : ∀ ω, θstar ω ∈ Θ ∩ ⋂ i, Θδ (ω i))
    (huniq : ∀ ω : Fin N → Δ, ∀ y ∈ Θ ∩ ⋂ i, Θδ (ω i),
      inner ℝ c y ≤ inner ℝ c (θstar ω) → y = θstar ω)
    (ε η : ℝ) (hη : 0 < η) (hηε : η < ε) (hε1 : ε ≤ 1) :
    Measure.pi (fun _ : Fin N => P) {ω | ε < (P {δ | θstar ω ∉ Θδ δ}).toReal} ≤
      ENNReal.ofReal (∑ i ∈ Finset.range d,
        (N.choose i : ℝ) * (ε - η) ^ i * (1 - (ε - η)) ^ (N - i)) := by
  classical
  set t := ε - η with ht
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ 1 := by linarith
  set B := ∑ i ∈ Finset.range d, (N.choose i : ℝ) * t ^ i * (1 - t) ^ (N - i) with hB
  have hB0 : 0 ≤ B := binSum_nonneg d N ht0 ht1
  set PN := Measure.pi (fun _ : Fin N => P) with hPN
  set A : Set (Fin N → Δ) := {ω | ε < (P {δ | θstar ω ∉ Θδ δ}).toReal} with hA
  have hnm : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∉ Θδ p.2} := hmeas.compl
  have hVm : Measurable fun θ : EuclideanSpace ℝ (Fin d) => (P {δ | θ ∉ Θδ δ}).toReal :=
    (measurable_measure_prodMk_left hnm).ennreal_toReal
  have hAm : MeasurableSet A := measurableSet_lt measurable_const (hVm.comp hθm)
  have key : ∀ L : ℕ, N ≤ L → 2 * (N : ℝ) ≤ η * L → 0 < L →
      (L.descFactorial N : ℝ) * (PN A).toReal ≤ (L : ℝ) ^ N * (B + 4 / (η ^ 2 * L)) := by
    intro L hNL hηL hL
    haveI : IsProbabilityMeasure (unifL L) := unifL_prob hL
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    set PL := Measure.pi (fun _ : Fin L => P) with hPL
    set U := Measure.pi (fun _ : Fin N => unifL L) with hU
    set Z : (Fin N → Fin L) → Set (Fin L → Δ) := fun κ =>
      {y | t < (unifL L {l | θstar (y ∘ κ) ∉ Θδ (y l)}).toReal} with hZ
    set δL : ℝ := 4 / (η ^ 2 * L) with hδL
    have hδL0 : 0 ≤ δL := by positivity
    have hcomp : ∀ κ : Fin N → Fin L, Measurable fun y : Fin L → Δ => y ∘ κ := fun κ =>
      measurable_pi_iff.2 fun i => measurable_pi_apply (κ i)
    have hZm : ∀ κ, MeasurableSet (Z κ) := by
      intro κ
      refine measurableSet_lt measurable_const ?_
      have : (fun y : Fin L → Δ => (unifL L {l | θstar (y ∘ κ) ∉ Θδ (y l)}).toReal) =
          fun y => ∑ l : Fin L, {y : Fin L → Δ | θstar (y ∘ κ) ∉ Θδ (y l)}.indicator
            (fun _ => (L : ℝ)⁻¹) y := by
        funext y
        rw [unifL_toReal]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp [Set.indicator]
      rw [this]
      refine Finset.measurable_sum _ fun l _ => measurable_const.indicator ?_
      exact (((hθm.comp (hcomp κ)).prodMk (measurable_pi_apply l)) hnm)
    -- (a) the finite theorem at every empirical sample
    have hF2 : ∀ y : Fin L → Δ,
        U {κ | t < (unifL L {l | θstar (y ∘ κ) ∉ Θδ (y l)}).toReal} ≤ ENNReal.ofReal B := by
      intro y
      have hne0 : ∀ T : Finset (Fin L), (Θ ∩ ⋂ k ∈ T, Θδ (y k)).Nonempty := by
        intro T
        obtain ⟨θ, hθ, hθi⟩ := hne T.card (fun i => y (T.equivFin.symm i))
        refine ⟨θ, hθ, ?_⟩
        simp only [Set.mem_iInter] at hθi ⊢
        intro k hk
        have := hθi (T.equivFin ⟨k, hk⟩)
        simpa using this
      exact finite_tail (Θk := fun l => Θδ (y l)) hd hΘ hΘc (fun l => hΘδ _) (fun l => hΘδc _)
        hne0 (unifL L) hN (fun κ => θstar (y ∘ κ)) (fun κ => hθs (y ∘ κ))
        (fun κ => huniq (y ∘ κ)) t ht0 ht1
    -- (b, c) averaging over the index maps
    have hU1 : ∀ κ : Fin N → Fin L, U {κ} = (L : ℝ≥0∞)⁻¹ ^ N := by
      intro κ
      rw [hU, Measure.pi_singleton]
      simp [unifL_singleton]
    have hUS : ∀ S : Set (Fin N → Fin L),
        U S = ∑ κ, S.indicator (fun _ => (L : ℝ≥0∞)⁻¹ ^ N) κ := by
      intro S
      rw [← lintegral_indicator_one (Set.to_countable S).measurableSet, lintegral_fintype]
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [hU1]
      by_cases h : κ ∈ S <;> simp [h]
    have hsum : (L : ℝ≥0∞)⁻¹ ^ N * ∑ κ : Fin N → Fin L, PL (Z κ) ≤ ENNReal.ofReal B := by
      calc (L : ℝ≥0∞)⁻¹ ^ N * ∑ κ : Fin N → Fin L, PL (Z κ)
          = ∑ κ : Fin N → Fin L,
              ∫⁻ y, (Z κ).indicator (fun _ => (L : ℝ≥0∞)⁻¹ ^ N) y ∂PL := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun κ _ => ?_
            rw [lintegral_indicator_const (hZm κ)]
        _ = ∫⁻ y, ∑ κ : Fin N → Fin L,
              (Z κ).indicator (fun _ => (L : ℝ≥0∞)⁻¹ ^ N) y ∂PL :=
            (lintegral_finset_sum _ fun κ _ => measurable_const.indicator (hZm κ)).symm
        _ = ∫⁻ y, U {κ | t < (unifL L {l | θstar (y ∘ κ) ∉ Θδ (y l)}).toReal} ∂PL := by
            refine lintegral_congr fun y => ?_
            rw [hUS]
            refine Finset.sum_congr rfl fun κ _ => ?_
            simp only [Set.indicator, hZ, Set.mem_setOf_eq]
        _ ≤ ∫⁻ _y, ENNReal.ofReal B ∂PL := lintegral_mono fun y => hF2 y
        _ = ENNReal.ofReal B := by simp [hPL]
    have hsum' : ∑ κ : Fin N → Fin L, PL (Z κ) ≤ (L : ℝ≥0∞) ^ N * ENNReal.ofReal B := by
      have hLL : (L : ℝ≥0∞) ^ N * (L : ℝ≥0∞)⁻¹ ^ N = 1 := by
        rw [← mul_pow, ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hL.ne')
          (ENNReal.natCast_ne_top L), one_pow]
      calc ∑ κ : Fin N → Fin L, PL (Z κ)
          = (L : ℝ≥0∞) ^ N * ((L : ℝ≥0∞)⁻¹ ^ N * ∑ κ : Fin N → Fin L, PL (Z κ)) := by
            rw [← mul_assoc, hLL, one_mul]
        _ ≤ (L : ℝ≥0∞) ^ N * ENNReal.ofReal B := by gcongr
    -- (d) one injective index map
    have hemb : ∀ κ : Fin N ↪ Fin L, PN A ≤ PL (Z κ) + ENNReal.ofReal δL := by
      intro κ
      set I := Finset.univ.map κ with hI
      have hsplit := pi_split P κ
      have hcardR : (Fintype.card {x // x ∉ I} : ℝ) = L - N := by
        rw [Fintype.card_subtype_compl, Fintype.card_coe, hI, Finset.card_map, Finset.card_univ,
          Fintype.card_fin, Fintype.card_fin, Nat.cast_sub hNL]
      have hmarg : PN A = PL {y | (fun i => y (κ i)) ∈ A} := by
        have := hsplit.measure_preimage (hAm.prod MeasurableSet.univ).nullMeasurableSet
        rw [Measure.prod_prod, measure_univ, mul_one] at this
        rw [← this]
        congr 1
        ext y
        simp
      set T : Set ((Fin N → Δ) × ({x // x ∉ I} → Δ)) := {p | p.1 ∈ A ∧
        (∑ j, {δ | θstar p.1 ∉ Θδ δ}.indicator (fun _ => (1:ℝ)) (p.2 j)) ≤ t * L} with hT
      have hTm : MeasurableSet T := by
        have hTeq : T = Prod.fst ⁻¹' A ∩ {p : (Fin N → Δ) × ({x // x ∉ I} → Δ) |
            (∑ j, {δ | θstar p.1 ∉ Θδ δ}.indicator (fun _ => (1:ℝ)) (p.2 j)) ≤ t * L} := rfl
        rw [hTeq]
        refine (measurable_fst hAm).inter (measurableSet_le ?_ measurable_const)
        refine Finset.measurable_sum _ fun j _ => ?_
        have : (fun p : (Fin N → Δ) × ({x // x ∉ I} → Δ) =>
            {δ | θstar p.1 ∉ Θδ δ}.indicator (fun _ => (1:ℝ)) (p.2 j)) =
            {p : (Fin N → Δ) × ({x // x ∉ I} → Δ) | θstar p.1 ∉ Θδ (p.2 j)}.indicator
              (fun _ => 1) := by
          funext p; simp [Set.indicator]
        rw [this]
        refine measurable_const.indicator ?_
        exact (show MeasurableSet ((fun p : (Fin N → Δ) × ({x // x ∉ I} → Δ) =>
            (θstar p.1, p.2 j)) ⁻¹' {q : EuclideanSpace ℝ (Fin d) × Δ | q.1 ∉ Θδ q.2}) from
          ((hθm.comp measurable_fst).prodMk ((measurable_pi_apply j).comp measurable_snd)) hnm)
      have hcover : {y : Fin L → Δ | (fun i => y (κ i)) ∈ A} ⊆ Z κ ∪
          (fun y : Fin L → Δ => ((fun i => y (κ i)), fun j : {x // x ∉ I} => y j)) ⁻¹' T := by
        intro y hy
        by_cases hz : y ∈ Z κ
        · exact Or.inl hz
        · right
          refine ⟨hy, ?_⟩
          simp only [hZ, Set.mem_setOf_eq, not_lt] at hz
          rw [unifL_toReal] at hz
          set f : Fin L → ℝ := fun l => {δ | θstar (y ∘ κ) ∉ Θδ δ}.indicator (fun _ => (1:ℝ)) (y l)
            with hf
          have hf0 : ∀ l, 0 ≤ f l := fun l => by
            simp only [hf, Set.indicator]; split_ifs <;> norm_num
          have h1 : ∑ j : {x // x ∉ I}, f j ≤ ∑ l : Fin L, f l := by
            rw [← Finset.sum_subtype Iᶜ (fun x => Finset.mem_compl) f]
            exact Finset.sum_le_univ_sum_of_nonneg hf0
          have h2 : ∑ l : Fin L, {l | θstar (y ∘ κ) ∉ Θδ (y l)}.indicator (fun _ => (L : ℝ)⁻¹) l =
              (L : ℝ)⁻¹ * ∑ l : Fin L, f l := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            simp only [hf, Set.indicator, Set.mem_setOf_eq]
            split_ifs <;> simp
          rw [h2] at hz
          have h3 : ∑ l : Fin L, f l ≤ t * L := by
            have := mul_le_mul_of_nonneg_left hz hLpos.le
            rw [← mul_assoc, mul_inv_cancel₀ hLpos.ne', one_mul] at this
            linarith
          exact h1.trans h3
      calc PN A = PL {y | (fun i => y (κ i)) ∈ A} := hmarg
        _ ≤ PL (Z κ ∪ (fun y : Fin L → Δ => ((fun i => y (κ i)),
              fun j : {x // x ∉ I} => y j)) ⁻¹' T) := measure_mono hcover
        _ ≤ PL (Z κ) + PL ((fun y : Fin L → Δ => ((fun i => y (κ i)),
              fun j : {x // x ∉ I} => y j)) ⁻¹' T) := measure_union_le _ _
        _ ≤ PL (Z κ) + ENNReal.ofReal δL := by
            gcongr
            rw [hsplit.measure_preimage hTm.nullMeasurableSet, Measure.prod_apply hTm]
            refine (lintegral_mono fun ω => ?_).trans
              (le_of_eq (by simp [hPN] : ∫⁻ _ω, ENNReal.ofReal δL ∂PN = ENNReal.ofReal δL))
            by_cases hω : ω ∈ A
            · have hBm : MeasurableSet {δ | θstar ω ∉ Θδ δ} := measurable_prodMk_left hnm
              set D : ℝ := ((L : ℝ) - N) * ε - t * L with hDdef
              have hNnn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
              have hLN : (N : ℝ) ≤ L := by exact_mod_cast hNL
              have hD : η * L / 2 ≤ D := by
                simp only [hDdef, ht]
                nlinarith
              have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
              have hv : ε < (P {δ | θstar ω ∉ Θδ δ}).toReal := hω
              have hsD : t * L + D ≤ (Fintype.card {x // x ∉ I} : ℝ) *
                  (P {δ | θstar ω ∉ Θδ δ}).toReal := by
                rw [hcardR]
                simp only [hDdef]
                nlinarith
              have hcheb := count_lower_tail P {δ | θstar ω ∉ Θδ δ} hBm (t * L) D hDpos hsD
              refine le_trans (measure_mono ?_) (hcheb.trans (ENNReal.ofReal_le_ofReal ?_))
              · intro z hz
                exact hz.2
              · rw [hcardR]
                have hD2 : (η * L / 2) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (by positivity) hD 2
                calc ((L : ℝ) - N) / D ^ 2 ≤ L / D ^ 2 :=
                      div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
                  _ ≤ L / (η * L / 2) ^ 2 :=
                      div_le_div_of_nonneg_left hLpos.le (by positivity) hD2
                  _ = δL := by
                      simp only [hδL]
                      field_simp
                      ring
            · have : Prod.mk ω ⁻¹' T = ∅ := by
                ext z
                simp [hT, hω]
              rw [this, measure_empty]
              exact bot_le
    -- (e) combine over all injective index maps
    have hcard : Fintype.card (Fin N ↪ Fin L) = L.descFactorial N := by
      rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
    have hcardle : (L.descFactorial N : ℝ≥0∞) ≤ (L : ℝ≥0∞) ^ N := by
      exact_mod_cast Nat.descFactorial_le_pow L N
    have hcomb : (L.descFactorial N : ℝ≥0∞) * PN A ≤
        (L : ℝ≥0∞) ^ N * (ENNReal.ofReal B + ENNReal.ofReal δL) := by
      calc (L.descFactorial N : ℝ≥0∞) * PN A = ∑ _κ : Fin N ↪ Fin L, PN A := by
            rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
        _ ≤ ∑ κ : Fin N ↪ Fin L, (PL (Z κ) + ENNReal.ofReal δL) :=
            Finset.sum_le_sum fun κ _ => hemb κ
        _ = ∑ κ : Fin N ↪ Fin L, PL (Z κ) + (L.descFactorial N : ℝ≥0∞) * ENNReal.ofReal δL := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
        _ ≤ ∑ κ : Fin N → Fin L, PL (Z κ) + (L : ℝ≥0∞) ^ N * ENNReal.ofReal δL := by
            gcongr ?_ + ?_
            · have := Finset.sum_map (Finset.univ : Finset (Fin N ↪ Fin L))
                ⟨fun κ : Fin N ↪ Fin L => (κ : Fin N → Fin L), DFunLike.coe_injective⟩
                (fun κ => PL (Z κ))
              simp only [Function.Embedding.coeFn_mk] at this
              rw [← this]
              exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
            · gcongr
        _ ≤ (L : ℝ≥0∞) ^ N * ENNReal.ofReal B + (L : ℝ≥0∞) ^ N * ENNReal.ofReal δL := by
            gcongr
        _ = (L : ℝ≥0∞) ^ N * (ENNReal.ofReal B + ENNReal.ofReal δL) := (mul_add _ _ _).symm
    have hfin : (L : ℝ≥0∞) ^ N * (ENNReal.ofReal B + ENNReal.ofReal δL) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top L))
        (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
    have := ENNReal.toReal_mono hfin hcomb
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_add ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hB0, ENNReal.toReal_ofReal hδL0,
      ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at this
    exact this
  -- the limit `L → ∞`
  set p := (PN A).toReal with hp
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hlim1 : Tendsto (fun L : ℕ => (((L : ℝ) + (1 - N)) / L) ^ N * p) atTop (𝓝 p) := by
    have h1 : Tendsto (fun L : ℕ => 1 + (1 - (N : ℝ)) / L) atTop (𝓝 1) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (1 - (N : ℝ))).const_add 1
    have h2 : Tendsto (fun L : ℕ => ((L : ℝ) + (1 - N)) / L) atTop (𝓝 1) := by
      refine h1.congr' ?_
      filter_upwards [eventually_ne_atTop 0] with L hL
      have : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hL
      field_simp
    simpa using (h2.pow N).mul_const p
  have hlim2 : Tendsto (fun L : ℕ => B + 4 / (η ^ 2 * L)) atTop (𝓝 B) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (4 / η ^ 2)).const_add B
    rw [add_zero] at h
    refine h.congr' (Eventually.of_forall fun L => ?_)
    simp only
    rw [div_div]
  have hev : ∀ᶠ L : ℕ in atTop, (((L : ℝ) + (1 - N)) / L) ^ N * p ≤ B + 4 / (η ^ 2 * L) := by
    obtain ⟨L0, hL0⟩ := exists_nat_ge (2 * (N : ℝ) / η)
    filter_upwards [eventually_ge_atTop (max (max N 1) L0)] with L hL
    have hNL : N ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
    have hL1 : 0 < L := lt_of_lt_of_le one_pos (le_trans (le_trans (le_max_right _ _)
      (le_max_left _ _)) hL)
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
    have hηL : 2 * (N : ℝ) ≤ η * L := by
      have h1 : (L0 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
      have h2 : 2 * (N : ℝ) / η ≤ L := hL0.trans h1
      rw [div_le_iff₀ hη] at h2
      linarith
    have hk := key L hNL hηL hL1
    have hdesc : (((L + 1 - N : ℕ) : ℝ)) ^ N ≤ (L.descFactorial N : ℝ) := by
      exact_mod_cast Nat.pow_sub_le_descFactorial L N
    have hcast : ((L + 1 - N : ℕ) : ℝ) = (L : ℝ) + (1 - N) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast] at hdesc
    have hbase : 0 ≤ (L : ℝ) + (1 - N) := by
      have : (N : ℝ) ≤ L := by exact_mod_cast hNL
      linarith
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (pow_pos hLpos N)]
    calc ((L : ℝ) + (1 - N)) ^ N * p ≤ (L.descFactorial N : ℝ) * p :=
          mul_le_mul_of_nonneg_right hdesc hp0
      _ ≤ (L : ℝ) ^ N * (B + 4 / (η ^ 2 * L)) := hk
      _ = (B + 4 / (η ^ 2 * L)) * (L : ℝ) ^ N := mul_comm _ _
  have hpB : p ≤ B := le_of_tendsto_of_tendsto hlim1 hlim2 hev
  rw [← ENNReal.ofReal_toReal (measure_ne_top PN A)]
  exact ENNReal.ofReal_le_ofReal hpB

end D8

end P3f312ca3

namespace P3f312ca3

/-- binomial tail `Σ_{i<d} C(N,i) ε^i (1-ε)^(N-i)`. -/
noncomputable def binTail (d N : ℕ) (ε : ℝ) : ℝ :=
  ∑ i ∈ Finset.range d, (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i)

theorem binTail_continuous (d N : ℕ) : Continuous (binTail d N) := by
  unfold binTail
  fun_prop

theorem binTail_zero {d N : ℕ} (hd : 1 ≤ d) : binTail d N 0 = 1 := by
  unfold binTail
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    simp [zero_pow hi]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

/-- K4: continuity of the binomial tail lets `η → 0⁺`. -/
theorem le_binTail_of_forall_sub {d N : ℕ} (μ : ℝ≥0∞) (ε : ℝ) (hε : 0 < ε)
    (h : ∀ η, 0 < η → η < ε → μ ≤ ENNReal.ofReal (binTail d N (ε - η))) :
    μ ≤ ENNReal.ofReal (binTail d N ε) := by
  have hc : Continuous fun η : ℝ => ENNReal.ofReal (binTail d N (ε - η)) :=
    ENNReal.continuous_ofReal.comp
      ((binTail_continuous d N).comp (continuous_const.sub continuous_id))
  have ht : Filter.Tendsto (fun η : ℝ => ENNReal.ofReal (binTail d N (ε - η)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (binTail d N ε))) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using this
  apply ge_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT hε] with η hη using h η hη.1 hη.2

end P3f312ca3

open ScenarioApproach.Generalization in
theorem solution
    {d N : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (c : EuclideanSpace ℝ (Fin d)) (Θ : Set (EuclideanSpace ℝ (Fin d)))
    (Θδ : Δ → Set (EuclideanSpace ℝ (Fin d)))
    (hΘ_convex : Convex ℝ Θ) (hΘ_closed : IsClosed Θ)
    (hΘδ_convex : ∀ δ, Convex ℝ (Θδ δ)) (hΘδ_closed : ∀ δ, IsClosed (Θδ δ))
    (hexu : ∀ (m : ℕ) (ω : Fin m → Δ), ∃! θ, IsSolution c Θ Θδ ω θ)
    (hmeas : MeasurableSet {p : EuclideanSpace ℝ (Fin d) × Δ | p.1 ∈ Θδ p.2})
    (θstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin d))
    (hθstar : ∀ ω, IsSolution c Θ Θδ ω (θstar ω)) (hθstar_meas : Measurable θstar)
    (hd : 1 ≤ d) (hN : d ≤ N) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin N => P) {ω | ε < violation P Θδ (θstar ω)} ≤
      ENNReal.ofReal
        (∑ i ∈ Finset.range d, (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i)) := by
  have hne : ∀ (m : ℕ) (ω : Fin m → Δ), (Θ ∩ ⋂ i, Θδ (ω i)).Nonempty := fun m ω =>
    let ⟨θ, hθ, _⟩ := hexu m ω
    ⟨θ, hθ.1⟩
  have huniq : ∀ ω : Fin N → Δ, ∀ y ∈ Θ ∩ ⋂ i, Θδ (ω i),
      inner ℝ c y ≤ inner ℝ c (θstar ω) → y = θstar ω := by
    intro ω y hy hcy
    obtain ⟨θ, _, hθu⟩ := hexu N ω
    have h1 : IsSolution c Θ Θδ ω y := ⟨hy, fun θ' hθ' => hcy.trans ((hθstar ω).2 θ' hθ')⟩
    exact (hθu y h1).trans (hθu (θstar ω) (hθstar ω)).symm
  rcases hε0.lt_or_eq with hpos | hzero
  · show _ ≤ ENNReal.ofReal (P3f312ca3.binTail d N ε)
    apply P3f312ca3.le_binTail_of_forall_sub _ ε hpos
    intro η hη hηε
    exact P3f312ca3.general_tail_eta hd P c Θ Θδ hΘ_convex hΘ_closed hΘδ_convex hΘδ_closed hne hmeas hN
      θstar hθstar_meas (fun ω => (hθstar ω).1) huniq ε η hη hηε hε1
  · subst hzero
    show _ ≤ ENNReal.ofReal (P3f312ca3.binTail d N 0)
    rw [P3f312ca3.binTail_zero hd, ENNReal.ofReal_one]
    exact MeasureTheory.prob_le_one
