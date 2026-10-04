-- Prove2me | solution 1 for TeschlQM.SelfAdjoint.selfAdjoint_extension_iff
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-03T21:02:28.89338+00:00
-- url     : https://prove2.me/submissions/b63841f0-e561-47ad-9f87-92f5794ece75

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_SelfAdjoint_defectSpace
import Definitions.Def_TeschlQM_SelfAdjoint_IsCayleyTransform
import Theorems.Thm_TeschlQM_SelfAdjoint_selfAdjoint_of_range_eq_top

open scoped InnerProductSpace ComplexConjugate
open Filter Topology

namespace TeschlQM.SelfAdjoint.VonNeumannAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma mem_rangeAdd_iff (A : H →ₗ.[ℂ] H) (z : ℂ) (x : H) :
    x ∈ rangeAdd A z ↔ ∃ ψ : A.domain, A ψ + z • (ψ : H) = x := by
  constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨⟨φ, φ.2⟩, ?_⟩
    show A ⟨φ, φ.2⟩ + z • (φ : H) = z • (φ : H) + A ⟨φ, φ.2⟩
    rw [add_comm]
  · rintro ⟨ψ, rfl⟩
    refine ⟨⟨ψ, ψ.2⟩, ?_⟩
    show z • (ψ : H) + A ψ = A ψ + z • (ψ : H)
    rw [add_comm]

/-- For symmetric `A`, `⟪ψ, Aψ⟫` is real. -/
lemma inner_self_apply_im (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (ψ : A.domain) :
    (⟪(ψ : H), A ψ⟫_ℂ).im = 0 := by
  have h := hA.2 ψ ψ
  have h2 : ⟪A ψ, (ψ : H)⟫_ℂ = conj ⟪(ψ : H), A ψ⟫_ℂ := (inner_conj_symm _ _).symm
  rw [h2] at h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith

/-- `|Im z| ‖ψ‖ ≤ ‖(A + z)ψ‖` for symmetric `A`. -/
lemma im_bound (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (z : ℂ) (ψ : A.domain) :
    |z.im| * ‖(ψ : H)‖ ≤ ‖A ψ + z • (ψ : H)‖ := by
  have hw : (⟪(ψ : H), A ψ + z • (ψ : H)⟫_ℂ).im = z.im * ‖(ψ : H)‖ ^ 2 := by
    rw [inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.add_im,
      inner_self_apply_im A hA ψ]
    simp [← Complex.ofReal_pow, Complex.mul_im]
  have h1 : |(⟪(ψ : H), A ψ + z • (ψ : H)⟫_ℂ).im| ≤ ‖(ψ : H)‖ * ‖A ψ + z • (ψ : H)‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  rw [hw, abs_mul, abs_of_nonneg (sq_nonneg ‖(ψ : H)‖), sq] at h1
  rcases (norm_nonneg (ψ : H)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · nlinarith

/-- For symmetric `A`, `‖(A + i)ψ‖ = ‖(A - i)ψ‖`. -/
lemma norm_add_I_eq_norm_sub_I (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A)
    (ψ : A.domain) : ‖A ψ + Complex.I • (ψ : H)‖ = ‖A ψ + (-Complex.I) • (ψ : H)‖ := by
  have hre : RCLike.re (⟪A ψ, Complex.I • (ψ : H)⟫_ℂ) = 0 := by
    rw [inner_smul_right]
    have hsym : ⟪A ψ, (ψ : H)⟫_ℂ = ⟪(ψ : H), A ψ⟫_ℂ := (hA.2 ψ ψ).symm
    have hreal : (⟪A ψ, (ψ : H)⟫_ℂ).im = 0 := by
      rw [hsym]; exact inner_self_apply_im A hA ψ
    simp [hreal]
  have h1 : ‖A ψ + Complex.I • (ψ : H)‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), hre, norm_smul, Complex.norm_I, one_mul]; ring
  have h2 : ‖A ψ + (-Complex.I) • (ψ : H)‖ ^ 2 = ‖A ψ‖ ^ 2 + ‖(ψ : H)‖ ^ 2 := by
    rw [neg_smul, ← sub_eq_add_neg, norm_sub_sq (𝕜 := ℂ), hre, norm_smul, Complex.norm_I,
      one_mul]; ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (h1.trans h2.symm)

/-- `A + z` as a linear map on `𝔇(A)`. -/
noncomputable def addZ (A : H →ₗ.[ℂ] H) (z : ℂ) : A.domain →ₗ[ℂ] H :=
  A.toFun + z • A.domain.subtype

lemma addZ_apply (A : H →ₗ.[ℂ] H) (z : ℂ) (ψ : A.domain) :
    addZ A z ψ = A ψ + z • (ψ : H) := rfl

lemma range_addZ (A : H →ₗ.[ℂ] H) (z : ℂ) : LinearMap.range (addZ A z) = rangeAdd A z := by
  ext x
  rw [mem_rangeAdd_iff, LinearMap.mem_range]
  rfl

lemma addZ_injective (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (z : ℂ)
    (hz : z.im ≠ 0) : Function.Injective (addZ A z) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ψ hψ
  have := im_bound A hA z ψ
  rw [← addZ_apply, hψ, norm_zero] at this
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  have : ‖(ψ : H)‖ ≤ 0 := by nlinarith [norm_nonneg (ψ : H)]
  exact Subtype.ext (norm_le_zero_iff.mp this)

lemma adjoint_apply_of_eq (A T : H →ₗ.[ℂ] H) (hT : T = A) (x : H) (h1 : x ∈ T.domain)
    (h2 : x ∈ A.domain) : T ⟨x, h1⟩ = A ⟨x, h2⟩ := by
  subst hT; rfl

variable [CompleteSpace H]

/-- For a self-adjoint `B` and non-real `z`, `Ran(B + z) = ℌ`. -/
lemma rangeAdd_eq_top_of_isSelfAdjoint (B : H →ₗ.[ℂ] H) (hSA : IsSelfAdjoint B) (z : ℂ)
    (hz : z.im ≠ 0) : rangeAdd B z = ⊤ := by
  have hdense : Dense (B.domain : Set H) := hSA.dense_domain
  have hB : TeschlQM.Shared.IsSymmetric B := by
    refine ⟨hdense, fun φ ψ => ?_⟩
    have hadj := LinearPMap.adjoint_isFormalAdjoint hdense (T := B)
    have h1 := hadj ⟨φ, by rw [LinearPMap.isSelfAdjoint_def.mp hSA]; exact φ.2⟩ ψ
    rw [adjoint_apply_of_eq B B.adjoint (LinearPMap.isSelfAdjoint_def.mp hSA) φ _ φ.2] at h1
    exact h1.symm
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  -- the range is closed
  have hcl : IsClosed (rangeAdd B z : Set H) := by
    refine IsSeqClosed.isClosed fun {y} {y₀} hy hlim => ?_
    have hy' : ∀ n, ∃ ψ : B.domain, B ψ + z • (ψ : H) = y n := fun n =>
      (mem_rangeAdd_iff B _ _).mp (hy n)
    choose ψ hψ using hy'
    have hcauchy : CauchySeq fun n => (ψ n : H) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq (|z.im| * ε) (mul_pos hpos hε)
      refine ⟨N, fun m hm k hk => ?_⟩
      have h1 := im_bound B hB z (ψ m - ψ k)
      have h2 : B (ψ m - ψ k) + z • ((ψ m - ψ k : B.domain) : H) = y m - y k := by
        rw [← hψ m, ← hψ k, LinearPMap.map_sub]
        simp only [Submodule.coe_sub, smul_sub]
        abel
      rw [h2] at h1
      rw [dist_eq_norm]
      have h3 := hN m hm k hk
      rw [dist_eq_norm] at h3
      simp only [Submodule.coe_sub] at h1
      by_contra! hcon
      nlinarith
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hBψ : Tendsto (fun n => B (ψ n)) atTop (𝓝 (y₀ - z • x)) := by
      have : (fun n => B (ψ n)) = fun n => y n - z • (ψ n : H) := by
        funext n; rw [← hψ n]; abel
      rw [this]
      exact hlim.sub (hx.const_smul z)
    have hmem : (x, y₀ - z • x) ∈ B.graph := by
      have hcl : IsClosed (B.graph : Set (H × H)) := hSA.isClosed
      refine hcl.mem_of_tendsto (hx.prodMk_nhds hBψ) (Eventually.of_forall fun n => ?_)
      exact (LinearPMap.mem_graph_iff B).mpr ⟨ψ n, rfl, rfl⟩
    obtain ⟨x', hx1, hx2⟩ := (LinearPMap.mem_graph_iff B).mp hmem
    refine (mem_rangeAdd_iff B _ _).mpr ⟨x', ?_⟩
    rw [hx2, hx1]
    simp
  -- the orthogonal complement is trivial
  have horth : (rangeAdd B z)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro φ hφ
    have hφ' : ∀ ψ : B.domain, ⟪B ψ + z • (ψ : H), φ⟫_ℂ = 0 := fun ψ =>
      (Submodule.mem_orthogonal _ _).mp hφ _ ((mem_rangeAdd_iff B _ _).mpr ⟨ψ, rfl⟩)
    have key : ∀ ψ : B.domain, ⟪(-conj z) • φ, (ψ : H)⟫_ℂ = ⟪φ, B ψ⟫_ℂ := by
      intro ψ
      have e : ⟪B ψ, φ⟫_ℂ = -(conj z * ⟪(ψ : H), φ⟫_ℂ) := by
        have := hφ' ψ
        rw [inner_add_left, inner_smul_left, add_eq_zero_iff_eq_neg] at this
        exact this
      rw [inner_smul_left, map_neg, Complex.conj_conj, ← inner_conj_symm φ (B ψ), e, map_neg,
        map_mul, Complex.conj_conj, inner_conj_symm, neg_mul]
    have hadj : φ ∈ B.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨(-conj z) • φ, key⟩
    have hval : B.adjoint ⟨φ, hadj⟩ = (-conj z) • φ :=
      LinearPMap.adjoint_apply_eq hdense _ key
    have hdom : φ ∈ B.domain := by
      have : B.adjoint.domain = B.domain := by rw [LinearPMap.isSelfAdjoint_def.mp hSA]
      exact this ▸ hadj
    have hBφ : B ⟨φ, hdom⟩ = (-conj z) • φ := by
      rw [← adjoint_apply_of_eq B B.adjoint (LinearPMap.isSelfAdjoint_def.mp hSA) φ hadj hdom,
        hval]
    have := im_bound B hB (conj z) ⟨φ, hdom⟩
    simp only at this
    rw [hBφ, neg_smul, neg_add_cancel, norm_zero, Complex.conj_im, abs_neg] at this
    have : ‖φ‖ ≤ 0 := by nlinarith [norm_nonneg φ]
    exact norm_le_zero_iff.mp this
  have := (Submodule.topologicalClosure_eq_top_iff (K := rangeAdd B z)).mpr horth
  rwa [IsClosed.submodule_topologicalClosure_eq hcl] at this

lemma isSymmetric_of_isSelfAdjoint (B : H →ₗ.[ℂ] H) (hSA : IsSelfAdjoint B) :
    TeschlQM.Shared.IsSymmetric B := by
  have hdense : Dense (B.domain : Set H) := hSA.dense_domain
  refine ⟨hdense, fun φ ψ => ?_⟩
  have hadj := LinearPMap.adjoint_isFormalAdjoint hdense (T := B)
  have h1 := hadj ⟨φ, by rw [LinearPMap.isSelfAdjoint_def.mp hSA]; exact φ.2⟩ ψ
  rw [adjoint_apply_of_eq B B.adjoint (LinearPMap.isSelfAdjoint_def.mp hSA) φ _ φ.2] at h1
  exact h1.symm

/-- Direction `⇒` of von Neumann's criterion: the Cayley transform of a self-adjoint extension
is a unitary of `ℌ` mapping `K₊` onto `K₋`. -/
lemma defect_equiv_of_extension (A B : H →ₗ.[ℂ] H) (hAB : A ≤ B) (hSA : IsSelfAdjoint B) :
    Nonempty (defectPlus A ≃ₗᵢ[ℂ] defectMinus A) := by
  have hB := isSymmetric_of_isSelfAdjoint B hSA
  have hIp : Complex.I.im ≠ 0 := by simp
  have hIm : (-Complex.I).im ≠ 0 := by simp
  have hsurjP : Function.Surjective (addZ B Complex.I) := LinearMap.range_eq_top.mp
    ((range_addZ B _).trans (rangeAdd_eq_top_of_isSelfAdjoint B hSA _ hIp))
  have hsurjM : Function.Surjective (addZ B (-Complex.I)) := LinearMap.range_eq_top.mp
    ((range_addZ B _).trans (rangeAdd_eq_top_of_isSelfAdjoint B hSA _ hIm))
  let eP := LinearEquiv.ofBijective (addZ B Complex.I) ⟨addZ_injective B hB _ hIp, hsurjP⟩
  let eM := LinearEquiv.ofBijective (addZ B (-Complex.I)) ⟨addZ_injective B hB _ hIm, hsurjM⟩
  let W0 : H ≃ₗ[ℂ] H := eP.symm.trans eM
  have hW0 : ∀ χ : B.domain, W0 (addZ B Complex.I χ) = addZ B (-Complex.I) χ := by
    intro χ
    show eM (eP.symm (eP χ)) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hnorm : ∀ y, ‖W0 y‖ = ‖y‖ := by
    intro y
    obtain ⟨χ, rfl⟩ := hsurjP y
    rw [hW0, addZ_apply, addZ_apply]
    exact (norm_add_I_eq_norm_sub_I B hB χ).symm
  let W : H ≃ₗᵢ[ℂ] H := { W0 with norm_map' := hnorm }
  have hWA : ∀ ψ : A.domain,
      W (A ψ + Complex.I • (ψ : H)) = A ψ + (-Complex.I) • (ψ : H) := by
    intro ψ
    have hψB : (ψ : H) ∈ B.domain := hAB.1 ψ.2
    have hBψ : B ⟨ψ, hψB⟩ = A ψ := (hAB.2 rfl).symm
    have := hW0 ⟨ψ, hψB⟩
    rw [addZ_apply, addZ_apply, hBψ] at this
    exact this
  have hplus : ∀ x ∈ defectPlus A, W x ∈ defectMinus A := by
    intro x hx
    rw [defectMinus, Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨ψ, rfl⟩ := (mem_rangeAdd_iff A _ _).mp hu
    rw [← hWA, W.inner_map_map]
    exact (Submodule.mem_orthogonal _ _).mp hx _ ((mem_rangeAdd_iff A _ _).mpr ⟨ψ, rfl⟩)
  have hminus : ∀ y ∈ defectMinus A, W.symm y ∈ defectPlus A := by
    intro y hy
    rw [defectPlus, Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨ψ, rfl⟩ := (mem_rangeAdd_iff A _ _).mp hu
    rw [← W.inner_map_map, W.apply_symm_apply, hWA]
    exact (Submodule.mem_orthogonal _ _).mp hy _ ((mem_rangeAdd_iff A _ _).mpr ⟨ψ, rfl⟩)
  exact ⟨{ toFun := fun x => ⟨W x, hplus x x.2⟩
           invFun := fun y => ⟨W.symm y, hminus y y.2⟩
           map_add' := fun x y => Subtype.ext (by simp)
           map_smul' := fun c x => Subtype.ext (by simp)
           left_inv := fun x => Subtype.ext (W.symm_apply_apply x)
           right_inv := fun y => Subtype.ext (W.apply_symm_apply y)
           norm_map' := fun x => W.norm_map x }⟩

omit [CompleteSpace H] in
/-- The inverse Cayley transform (Teschl, Theorem 2.25): an isometric `V` with `Ran(1 - V)`
dense is the Cayley transform of a symmetric operator. -/
lemma exists_symmetric_of_isometric (V : H →ₗ.[ℂ] H) (hV : IsIsometric V)
    (hdense : Dense (rangeOneSub V : Set H)) :
    ∃ A : H →ₗ.[ℂ] H, TeschlQM.Shared.IsSymmetric A ∧ IsCayleyTransform A V := by
  have h2I : (2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  let Vi : V.domain →ₗᵢ[ℂ] H := { toLinearMap := V.toFun, norm_map' := hV }
  have hinner : ∀ φ η : V.domain, ⟪V φ, V η⟫_ℂ = ⟪(φ : H), (η : H)⟫_ℂ :=
    fun φ η => Vi.inner_map_map φ η
  let oneSub : V.domain →ₗ[ℂ] H := V.domain.subtype - V.toFun
  have oneSub_apply : ∀ φ : V.domain, oneSub φ = (φ : H) - V φ := fun φ => rfl
  have hinj : Function.Injective oneSub := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro φ hφ
    rw [oneSub_apply] at hφ
    have hφ' : (φ : H) = V φ := sub_eq_zero.mp hφ
    have horth : ∀ y ∈ (rangeOneSub V : Set H), ⟪(φ : H), y⟫_ℂ = 0 := by
      rintro y ⟨η, rfl⟩
      show ⟪(φ : H), (η : H) - V η⟫_ℂ = 0
      rw [inner_sub_right, ← hinner φ η, ← hφ', sub_self]
    have h0 : ⟪(φ : H), (φ : H)⟫_ℂ = 0 :=
      ((isClosed_eq (continuous_const.inner continuous_id) continuous_const).closure_subset_iff.mpr
        horth) (hdense (φ : H))
    exact Subtype.ext (inner_self_eq_zero.mp h0)
  let e := LinearEquiv.ofInjective oneSub hinj
  let A : H →ₗ.[ℂ] H :=
    { domain := LinearMap.range oneSub
      toFun := (Complex.I • (V.domain.subtype + V.toFun)) ∘ₗ e.symm.toLinearMap }
  have memA : ∀ φ : V.domain, oneSub φ ∈ A.domain := fun φ => ⟨φ, rfl⟩
  have hAapp : ∀ (φ : V.domain) (h : oneSub φ ∈ A.domain),
      A ⟨oneSub φ, h⟩ = Complex.I • ((φ : H) + V φ) := by
    intro φ h
    show (Complex.I • (V.domain.subtype + V.toFun)) (e.symm ⟨oneSub φ, h⟩) = _
    have : e.symm ⟨oneSub φ, h⟩ = φ := by
      rw [LinearEquiv.symm_apply_eq]
      ext
      rw [LinearEquiv.ofInjective_apply]
    rw [this]
    rfl
  have hAform : ∀ ψ : A.domain, ∃ φ : V.domain, ∃ h : oneSub φ ∈ A.domain,
      ψ = ⟨oneSub φ, h⟩ := by
    intro ψ
    obtain ⟨φ, hφ⟩ := LinearMap.mem_range.mp ψ.2
    exact ⟨φ, memA φ, Subtype.ext hφ.symm⟩
  have hplus : ∀ (φ : V.domain) (h : oneSub φ ∈ A.domain),
      A ⟨oneSub φ, h⟩ + Complex.I • oneSub φ = (2 * Complex.I) • (φ : H) := by
    intro φ h
    rw [hAapp, oneSub_apply, two_mul, add_smul, smul_add, smul_sub]; abel
  have hminus : ∀ (φ : V.domain) (h : oneSub φ ∈ A.domain),
      A ⟨oneSub φ, h⟩ - Complex.I • oneSub φ = (2 * Complex.I) • V φ := by
    intro φ h
    rw [hAapp, oneSub_apply, two_mul, add_smul, smul_add, smul_sub]; abel
  refine ⟨A, ⟨hdense, ?_⟩, ?_, ?_⟩
  · intro ψ₁ ψ₂
    obtain ⟨φ₁, h₁, rfl⟩ := hAform ψ₁
    obtain ⟨φ₂, h₂, rfl⟩ := hAform ψ₂
    show ⟪oneSub φ₁, A ⟨oneSub φ₂, h₂⟩⟫_ℂ = ⟪A ⟨oneSub φ₁, h₁⟩, oneSub φ₂⟫_ℂ
    rw [hAapp, hAapp, oneSub_apply, oneSub_apply]
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, hinner, Complex.conj_I]
    ring
  · ext x
    rw [mem_rangeAdd_iff]
    constructor
    · intro hx
      let φ : V.domain := (2 * Complex.I)⁻¹ • ⟨x, hx⟩
      refine ⟨⟨oneSub φ, memA φ⟩, (hplus φ (memA φ)).trans ?_⟩
      show (2 * Complex.I) • ((2 * Complex.I)⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ h2I, one_smul]
    · rintro ⟨ψ, rfl⟩
      obtain ⟨φ, h, rfl⟩ := hAform ψ
      rw [hplus]
      exact V.domain.smul_mem _ φ.2
  · intro ψ h
    obtain ⟨φ, hφ, rfl⟩ := hAform ψ
    have hel : (⟨_, h⟩ : V.domain) = (2 * Complex.I) • φ := Subtype.ext (hplus φ hφ)
    rw [hel, LinearPMap.map_smul, hminus]

/-- Direction `⇐` of von Neumann's criterion: a unitary `K₊ → K₋` together with the closure of
the Cayley transform of `A` gives a unitary of `ℌ` extending the Cayley transform, whose inverse
Cayley transform is a self-adjoint extension of `A`. -/
lemma extension_of_defect_equiv (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A)
    (U : defectPlus A ≃ₗᵢ[ℂ] defectMinus A) : ∃ B : H →ₗ.[ℂ] H, A ≤ B ∧ IsSelfAdjoint B := by
  have hIp : Complex.I.im ≠ 0 := by simp
  have hIm : (-Complex.I).im ≠ 0 := by simp
  have h2I : (2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  set S := rangeAdd A Complex.I with hS
  set T := rangeAdd A (-Complex.I) with hT
  have memS : ∀ ψ : A.domain, addZ A Complex.I ψ ∈ S := fun ψ =>
    (mem_rangeAdd_iff A _ _).mpr ⟨ψ, rfl⟩
  have memT : ∀ ψ : A.domain, addZ A (-Complex.I) ψ ∈ T := fun ψ =>
    (mem_rangeAdd_iff A _ _).mpr ⟨ψ, rfl⟩
  -- the Cayley transform `Ran(A + i) ≃ Ran(A - i)`
  let p : A.domain →ₗ[ℂ] S := LinearMap.codRestrict S (addZ A Complex.I) memS
  let m : A.domain →ₗ[ℂ] T := LinearMap.codRestrict T (addZ A (-Complex.I)) memT
  have hp : Function.Bijective p := by
    refine ⟨fun a b h => addZ_injective A hA _ hIp (congrArg Subtype.val h), fun s => ?_⟩
    obtain ⟨ψ, hψ⟩ := (mem_rangeAdd_iff A _ _).mp s.2
    exact ⟨ψ, Subtype.ext hψ⟩
  have hm : Function.Bijective m := by
    refine ⟨fun a b h => addZ_injective A hA _ hIm (congrArg Subtype.val h), fun s => ?_⟩
    obtain ⟨ψ, hψ⟩ := (mem_rangeAdd_iff A _ _).mp s.2
    exact ⟨ψ, Subtype.ext hψ⟩
  let eP := LinearEquiv.ofBijective p hp
  let eM := LinearEquiv.ofBijective m hm
  let f : S ≃ₗ[ℂ] T := eP.symm.trans eM
  have hf : ∀ ψ, f (p ψ) = m ψ := by
    intro ψ
    show eM (eP.symm (eP ψ)) = m ψ
    rw [LinearEquiv.symm_apply_apply]
    rfl
  -- its extension to the closures
  let Sb := S.topologicalClosure
  let Tb := T.topologicalClosure
  have : CompleteSpace Sb := S.isClosed_topologicalClosure.completeSpace_coe
  have : CompleteSpace Tb := T.isClosed_topologicalClosure.completeSpace_coe
  let e₁ : S →ₗ[ℂ] Sb := Submodule.inclusion S.le_topologicalClosure
  let e₂ : T →ₗ[ℂ] Tb := Submodule.inclusion T.le_topologicalClosure
  have hd₁ : DenseRange e₁ :=
    (denseRange_inclusion_iff (s := (S : Set H)) (t := (Sb : Set H))
      S.le_topologicalClosure).mpr (by rw [Submodule.topologicalClosure_coe])
  have hd₂ : DenseRange e₂ :=
    (denseRange_inclusion_iff (s := (T : Set H)) (t := (Tb : Set H))
      T.le_topologicalClosure).mpr (by rw [Submodule.topologicalClosure_coe])
  have hn : ∀ x : S, ‖e₂ (f x)‖ = ‖e₁ x‖ := by
    intro x
    obtain ⟨ψ, rfl⟩ := hp.2 x
    rw [hf]
    show ‖addZ A (-Complex.I) ψ‖ = ‖addZ A Complex.I ψ‖
    rw [addZ_apply, addZ_apply]
    exact (norm_add_I_eq_norm_sub_I A hA ψ).symm
  let Vb : Sb ≃ₗᵢ[ℂ] Tb := f.extendOfIsometry e₁ e₂ hd₁ hd₂ hn
  have hVb : ∀ ψ : A.domain, (Vb (e₁ (p ψ)) : H) = A ψ + (-Complex.I) • (ψ : H) := by
    intro ψ
    show ((f.extendOfIsometry e₁ e₂ hd₁ hd₂ hn) (e₁ (p ψ)) : H) = _
    rw [LinearEquiv.extendOfIsometry_eq, hf]
    rfl
  -- orthogonal decompositions `ℌ = closure Ran(A ± i) ⊕ K±`
  have hKp : defectPlus A = Sbᗮ := (Submodule.orthogonal_closure S).symm
  have hKm : defectMinus A = Tbᗮ := (Submodule.orthogonal_closure T).symm
  have hcP : IsCompl Sb Sbᗮ := Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  have hcM : IsCompl Tb Tbᗮ := Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  let dP := Submodule.prodEquivOfIsCompl Sb Sbᗮ hcP
  let dM := Submodule.prodEquivOfIsCompl Tb Tbᗮ hcM
  have hdP : ∀ q, dP q = (q.1 : H) + q.2 := fun q => Submodule.coe_prodEquivOfIsCompl' _ _ hcP q
  have hdM : ∀ q, dM q = (q.1 : H) + q.2 := fun q => Submodule.coe_prodEquivOfIsCompl' _ _ hcM q
  let U' : Sbᗮ ≃ₗᵢ[ℂ] Tbᗮ :=
    ((LinearIsometryEquiv.ofEq _ _ hKp.symm).trans U).trans (LinearIsometryEquiv.ofEq _ _ hKm)
  -- the unitary `W = V̄ ⊕ U`
  let W0 : H ≃ₗ[ℂ] H := dP.symm.trans ((Vb.toLinearEquiv.prodCongr U'.toLinearEquiv).trans dM)
  have hW0 : ∀ q : Sb × Sbᗮ, W0 (dP q) = (Vb q.1 : H) + (U' q.2 : H) := by
    intro q
    show dM ((Vb.toLinearEquiv.prodCongr U'.toLinearEquiv) (dP.symm (dP q))) = _
    rw [LinearEquiv.symm_apply_apply, hdM]
    rfl
  have hnormW : ∀ x, ‖W0 x‖ = ‖x‖ := by
    intro x
    obtain ⟨q, rfl⟩ := dP.surjective x
    rw [hW0, hdP]
    have h1 : ⟪(Vb q.1 : H), (U' q.2 : H)⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (Vb q.1).2 (U' q.2).2
    have h2 : ⟪(q.1 : H), (q.2 : H)⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal q.1.2 q.2.2
    have e1 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h1
    have e2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h2
    have n1 : ‖(Vb q.1 : H)‖ = ‖(q.1 : H)‖ := Vb.norm_map q.1
    have n2 : ‖(U' q.2 : H)‖ = ‖(q.2 : H)‖ := U'.norm_map q.2
    rw [n1, n2, ← e2] at e1
    exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp e1
  let W : H ≃ₗᵢ[ℂ] H := { W0 with norm_map' := hnormW }
  have hWA : ∀ ψ : A.domain,
      W (A ψ + Complex.I • (ψ : H)) = A ψ + (-Complex.I) • (ψ : H) := by
    intro ψ
    have hq : A ψ + Complex.I • (ψ : H) = dP (e₁ (p ψ), 0) := by
      rw [hdP]
      simp only [Submodule.coe_zero, add_zero]
      rfl
    show W0 _ = _
    rw [hq, hW0, hVb]
    simp
  -- the partial isometry `V₁ := W` with domain `ℌ`
  let V₁ : H →ₗ.[ℂ] H :=
    { domain := ⊤
      toFun := (W.toLinearEquiv.toLinearMap) ∘ₗ (⊤ : Submodule ℂ H).subtype }
  have hV₁ : ∀ x : V₁.domain, V₁ x = W x := fun x => rfl
  have hiso : IsIsometric V₁ := fun x => W.norm_map x
  have hdense : Dense (rangeOneSub V₁ : Set H) := by
    apply hA.1.mono
    intro ψ hψ
    let ψ' : A.domain := ⟨ψ, hψ⟩
    let φ : V₁.domain := ⟨(2 * Complex.I)⁻¹ • (A ψ' + Complex.I • ψ), Submodule.mem_top⟩
    refine ⟨φ, ?_⟩
    show (φ : H) - V₁ φ = ψ
    rw [hV₁]
    show (2 * Complex.I)⁻¹ • (A ψ' + Complex.I • ψ) -
      W ((2 * Complex.I)⁻¹ • (A ψ' + Complex.I • ψ)) = ψ
    rw [LinearIsometryEquiv.map_smul, hWA ψ', ← smul_sub]
    have : A ψ' + Complex.I • (ψ' : H) - (A ψ' + (-Complex.I) • (ψ' : H)) =
        (2 * Complex.I) • (ψ' : H) := by
      rw [two_mul, add_smul, neg_smul]; abel
    rw [this, smul_smul, inv_mul_cancel₀ h2I, one_smul]
  obtain ⟨B, hB, hBV⟩ := exists_symmetric_of_isometric V₁ hiso hdense
  -- `A ⊆ B`
  have hAB : A ≤ B := by
    have key : ∀ ψ : A.domain, ∃ h : (ψ : H) ∈ B.domain, B ⟨ψ, h⟩ = A ψ := by
      intro ψ
      have hx : A ψ + Complex.I • (ψ : H) ∈ rangeAdd B Complex.I := by
        rw [← hBV.1]; exact Submodule.mem_top
      obtain ⟨χ, hχ⟩ := (mem_rangeAdd_iff B _ _).mp hx
      have hc : B χ + Complex.I • (χ : H) ∈ V₁.domain := Submodule.mem_top
      have e1 := hBV.2 χ hc
      rw [hV₁] at e1
      have e1' : W (B χ + Complex.I • (χ : H)) = B χ - Complex.I • (χ : H) := e1
      rw [hχ, hWA] at e1'
      have hψχ : (ψ : H) = χ := by
        have : (2 * Complex.I) • (ψ : H) = (2 * Complex.I) • (χ : H) := by
          calc (2 * Complex.I) • (ψ : H)
              = (A ψ + Complex.I • (ψ : H)) - (A ψ + (-Complex.I) • (ψ : H)) := by
                rw [two_mul, add_smul, neg_smul]; abel
            _ = (B χ + Complex.I • (χ : H)) - (B χ - Complex.I • (χ : H)) := by rw [hχ, e1']
            _ = (2 * Complex.I) • (χ : H) := by rw [two_mul, add_smul]; abel
        exact smul_right_injective H h2I this
      refine ⟨hψχ ▸ χ.2, ?_⟩
      have hBA : B χ = A ψ := by
        have : (2 : ℂ) • B χ = (2 : ℂ) • A ψ := by
          calc (2 : ℂ) • B χ = (B χ + Complex.I • (χ : H)) + (B χ - Complex.I • (χ : H)) := by
                rw [two_smul]; abel
            _ = (A ψ + Complex.I • (ψ : H)) + (A ψ + (-Complex.I) • (ψ : H)) := by rw [hχ, e1']
            _ = (2 : ℂ) • A ψ := by rw [two_smul, neg_smul]; abel
        exact smul_right_injective H two_ne_zero this
      rw [← hBA]
      congr 1
      exact Subtype.ext hψχ
    refine ⟨fun x hx => (key ⟨x, hx⟩).1, fun x y hxy => ?_⟩
    obtain ⟨hx, hBx⟩ := key x
    rw [← hBx]
    congr 1
    exact Subtype.ext hxy
  -- `B` is self-adjoint by Lemma 2.3
  refine ⟨B, hAB, selfAdjoint_of_range_eq_top B hB Complex.I ?_ ?_⟩
  · rw [← hBV.1]
  · rw [Complex.conj_I, eq_top_iff]
    intro y _
    have hx : W.symm y ∈ rangeAdd B Complex.I := by
      rw [← hBV.1]; exact Submodule.mem_top
    obtain ⟨χ, hχ⟩ := (mem_rangeAdd_iff B _ _).mp hx
    have e1 := hBV.2 χ Submodule.mem_top
    refine (mem_rangeAdd_iff B _ _).mpr ⟨χ, ?_⟩
    rw [neg_smul, ← sub_eq_add_neg, ← e1]
    show W (B χ + Complex.I • (χ : H)) = y
    rw [hχ, W.apply_symm_apply]

end TeschlQM.SelfAdjoint.VonNeumannAux

open TeschlQM.SelfAdjoint TeschlQM.SelfAdjoint.VonNeumannAux in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) :
    (∃ B : H →ₗ.[ℂ] H, A ≤ B ∧ IsSelfAdjoint B) ↔ HasEqualDefectIndices A := by
  constructor
  · rintro ⟨B, hAB, hSA⟩
    exact defect_equiv_of_extension A B hAB hSA
  · rintro ⟨U⟩
    exact extension_of_defect_equiv A hA U
