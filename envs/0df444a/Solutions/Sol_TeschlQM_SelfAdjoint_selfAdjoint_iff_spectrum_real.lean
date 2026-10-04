-- Prove2me | solution 1 for TeschlQM.SelfAdjoint.selfAdjoint_iff_spectrum_real
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-03T20:48:11.095565+00:00
-- url     : https://prove2.me/submissions/206ea4e3-4744-4ca2-9f72-04fdf1f0c30f

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsSymmetric
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_SelfAdjoint_addScalar
import Theorems.Thm_TeschlQM_SelfAdjoint_selfAdjoint_of_range_eq_top

open scoped InnerProductSpace ComplexConjugate
open Filter Topology

namespace TeschlQM.SelfAdjoint.SpecAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `A - z` as a linear map on `𝔇(A)`. -/
noncomputable def subZ (A : H →ₗ.[ℂ] H) (z : ℂ) : A.domain →ₗ[ℂ] H :=
  A.toFun - z • A.domain.subtype

lemma subZ_apply (A : H →ₗ.[ℂ] H) (z : ℂ) (ψ : A.domain) :
    subZ A z ψ = A ψ - z • (ψ : H) := rfl

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

/-- `|Im z| ‖ψ‖ ≤ ‖(A - z)ψ‖` for symmetric `A`. -/
lemma im_bound (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (z : ℂ) (ψ : A.domain) :
    |z.im| * ‖(ψ : H)‖ ≤ ‖A ψ - z • (ψ : H)‖ := by
  have hw : (⟪(ψ : H), A ψ - z • (ψ : H)⟫_ℂ).im = -(z.im * ‖(ψ : H)‖ ^ 2) := by
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.sub_im,
      inner_self_apply_im A hA ψ]
    simp [← Complex.ofReal_pow, Complex.mul_im]
  have h1 : |(⟪(ψ : H), A ψ - z • (ψ : H)⟫_ℂ).im| ≤ ‖(ψ : H)‖ * ‖A ψ - z • (ψ : H)‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  rw [hw, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg ‖(ψ : H)‖), sq] at h1
  rcases (norm_nonneg (ψ : H)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · nlinarith

/-- `(E - l) ‖ψ‖ ≤ ‖(A - l)ψ‖` if `A - E ≥ 0`. -/
lemma re_bound (A : H →ₗ.[ℂ] H) (E l : ℝ)
    (hE : ∀ ψ : A.domain, E * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re) (ψ : A.domain) :
    (E - l) * ‖(ψ : H)‖ ≤ ‖A ψ - (l : ℂ) • (ψ : H)‖ := by
  have hw : (⟪(ψ : H), A ψ - (l : ℂ) • (ψ : H)⟫_ℂ).re =
      (⟪(ψ : H), A ψ⟫_ℂ).re - l * ‖(ψ : H)‖ ^ 2 := by
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.sub_re]
    simp [← Complex.ofReal_pow, Complex.mul_re]
  have h1 : (⟪(ψ : H), A ψ - (l : ℂ) • (ψ : H)⟫_ℂ).re ≤ ‖(ψ : H)‖ * ‖A ψ - (l : ℂ) • (ψ : H)‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  rw [hw] at h1
  have h2 := hE ψ
  rcases (norm_nonneg (ψ : H)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · have : (E - l) * ‖(ψ : H)‖ ^ 2 ≤ ‖(ψ : H)‖ * ‖A ψ - (l : ℂ) • (ψ : H)‖ := by nlinarith
    rw [sq, ← mul_assoc, mul_comm _ ‖(ψ : H)‖] at this
    exact le_of_mul_le_mul_left (by rw [mul_comm]; linarith) hpos

/-- A lower bound `c ‖ψ‖ ≤ ‖(A - z)ψ‖` bounds every resolvent at `z` by `c⁻¹`. -/
lemma norm_resolvent_le (A : H →ₗ.[ℂ] H) (z : ℂ) (c : ℝ) (hc : 0 < c)
    (hb : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ - z • (ψ : H)‖) (R : H →L[ℂ] H)
    (hR : TeschlQM.Shared.IsResolventAt A z R) : ‖R‖ ≤ c⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le) fun φ => ?_
  obtain ⟨h, hφ⟩ := hR.1 φ
  have := hb ⟨R φ, h⟩
  simp only at this
  rw [hφ] at this
  rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
  exact this

variable [CompleteSpace H]

/-- A closed operator with `c ‖ψ‖ ≤ ‖(A - z)ψ‖` has closed `Ran(A - z)`. -/
lemma isClosed_range_subZ (A : H →ₗ.[ℂ] H) (hAc : A.IsClosed) (z : ℂ) (c : ℝ) (hc : 0 < c)
    (hb : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ - z • (ψ : H)‖) :
    IsClosed (Set.range (subZ A z)) := by
  refine IsSeqClosed.isClosed fun {y} {y₀} hy hlim => ?_
  choose ψ hψ using hy
  have hcauchy : CauchySeq fun n => (ψ n : H) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq (c * ε) (mul_pos hc hε)
    refine ⟨N, fun m hm k hk => ?_⟩
    have h1 := hb (ψ m - ψ k)
    have h2 : A (ψ m - ψ k) - z • ((ψ m - ψ k : A.domain) : H) = y m - y k := by
      rw [← hψ m, ← hψ k, subZ_apply, subZ_apply, LinearPMap.map_sub]
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
  have hAψ : Tendsto (fun n => A (ψ n)) atTop (𝓝 (y₀ + z • x)) := by
    have : (fun n => A (ψ n)) = fun n => y n + z • (ψ n : H) := by
      funext n; rw [← hψ n, subZ_apply]; abel
    rw [this]
    exact hlim.add (hx.const_smul z)
  have hmem : (x, y₀ + z • x) ∈ A.graph := by
    have hcl : IsClosed (A.graph : Set (H × H)) := hAc
    refine hcl.mem_of_tendsto (hx.prodMk_nhds hAψ) (Eventually.of_forall fun n => ?_)
    exact (LinearPMap.mem_graph_iff A).mpr ⟨ψ n, rfl, rfl⟩
  obtain ⟨x', hx1, hx2⟩ := (LinearPMap.mem_graph_iff A).mp hmem
  refine ⟨x', ?_⟩
  rw [subZ_apply, hx2, hx1]
  simp

omit [CompleteSpace H] in
lemma adjoint_apply_of_eq (A T : H →ₗ.[ℂ] H) (hT : T = A) (x : H) (h1 : x ∈ T.domain)
    (h2 : x ∈ A.domain) : T ⟨x, h1⟩ = A ⟨x, h2⟩ := by
  subst hT; rfl

/-- For self-adjoint `A` with lower bounds at `z` and `z*`, `Ran(A - z) = ℌ`. -/
lemma range_subZ_eq_top (A : H →ₗ.[ℂ] H) (hSA : IsSelfAdjoint A) (z : ℂ) (c c' : ℝ)
    (hc : 0 < c) (hc' : 0 < c')
    (hb : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ - z • (ψ : H)‖)
    (hb' : ∀ ψ : A.domain, c' * ‖(ψ : H)‖ ≤ ‖A ψ - conj z • (ψ : H)‖) :
    LinearMap.range (subZ A z) = ⊤ := by
  have hcl : IsClosed (LinearMap.range (subZ A z) : Set H) :=
    isClosed_range_subZ A hSA.isClosed z c hc hb
  have hdense : Dense (A.domain : Set H) := hSA.dense_domain
  have horth : (LinearMap.range (subZ A z))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro φ hφ
    have hφ' : ∀ ψ : A.domain, ⟪A ψ - z • (ψ : H), φ⟫_ℂ = 0 := fun ψ =>
      (Submodule.mem_orthogonal _ _).mp hφ _ ⟨ψ, rfl⟩
    have key : ∀ ψ : A.domain, ⟪conj z • φ, (ψ : H)⟫_ℂ = ⟪φ, A ψ⟫_ℂ := by
      intro ψ
      have e : ⟪A ψ, φ⟫_ℂ = conj z * ⟪(ψ : H), φ⟫_ℂ := by
        have := hφ' ψ
        rw [inner_sub_left, inner_smul_left, sub_eq_zero] at this
        exact this
      rw [inner_smul_left, Complex.conj_conj, ← inner_conj_symm φ (A ψ), e, map_mul,
        Complex.conj_conj, inner_conj_symm]
    have hadj : φ ∈ A.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨conj z • φ, key⟩
    have hval : A.adjoint ⟨φ, hadj⟩ = conj z • φ :=
      LinearPMap.adjoint_apply_eq hdense _ key
    have hdom : φ ∈ A.domain := by
      have : A.adjoint.domain = A.domain := by rw [LinearPMap.isSelfAdjoint_def.mp hSA]
      exact this ▸ hadj
    have hAφ : A ⟨φ, hdom⟩ = conj z • φ := by
      rw [← adjoint_apply_of_eq A A.adjoint (LinearPMap.isSelfAdjoint_def.mp hSA) φ hadj hdom, hval]
    have := hb' ⟨φ, hdom⟩
    simp only at this
    rw [hAφ, sub_self, norm_zero] at this
    have : ‖φ‖ ≤ 0 := by nlinarith [norm_nonneg φ]
    exact norm_le_zero_iff.mp this
  have := (Submodule.topologicalClosure_eq_top_iff (K := LinearMap.range (subZ A z))).mpr horth
  rwa [IsClosed.submodule_topologicalClosure_eq hcl] at this

omit [CompleteSpace H] in
/-- Surjectivity of `A - z` plus a lower bound gives a bounded resolvent. -/
lemma exists_resolvent (A : H →ₗ.[ℂ] H) (z : ℂ) (c : ℝ) (hc : 0 < c)
    (hb : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ - z • (ψ : H)‖)
    (hsurj : LinearMap.range (subZ A z) = ⊤) :
    ∃ R : H →L[ℂ] H, TeschlQM.Shared.IsResolventAt A z R := by
  have hinj : Function.Injective (subZ A z) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ψ hψ
    have := hb ψ
    rw [← subZ_apply, hψ, norm_zero] at this
    have : ‖(ψ : H)‖ ≤ 0 := by nlinarith [norm_nonneg (ψ : H)]
    exact Subtype.ext (norm_le_zero_iff.mp this)
  let e := LinearEquiv.ofBijective (subZ A z) ⟨hinj, LinearMap.range_eq_top.mp hsurj⟩
  have he : ∀ φ : H, subZ A z (e.symm φ) = φ := fun φ => e.apply_symm_apply φ
  let R0 : H →ₗ[ℂ] H := A.domain.subtype ∘ₗ e.symm.toLinearMap
  have hbound : ∀ φ : H, ‖R0 φ‖ ≤ c⁻¹ * ‖φ‖ := by
    intro φ
    have := hb (e.symm φ)
    rw [← subZ_apply, he] at this
    rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact this
  refine ⟨R0.mkContinuous c⁻¹ hbound, ?_, ?_⟩
  · intro φ
    refine ⟨(e.symm φ).2, ?_⟩
    have := he φ
    rw [subZ_apply] at this
    exact this
  · intro ψ
    show ((e.symm (subZ A z ψ) : A.domain) : H) = ψ
    have : e.symm (subZ A z ψ) = ψ := e.symm_apply_apply ψ
    rw [this]

/-- For self-adjoint `A` with lower bounds at `z` and `z*`, `z ∈ ρ(A)`. -/
lemma mem_resolventSet (A : H →ₗ.[ℂ] H) (hSA : IsSelfAdjoint A) (z : ℂ) (c c' : ℝ)
    (hc : 0 < c) (hc' : 0 < c')
    (hb : ∀ ψ : A.domain, c * ‖(ψ : H)‖ ≤ ‖A ψ - z • (ψ : H)‖)
    (hb' : ∀ ψ : A.domain, c' * ‖(ψ : H)‖ ≤ ‖A ψ - conj z • (ψ : H)‖) :
    z ∈ TeschlQM.Shared.resolventSet A :=
  exists_resolvent A z c hc hb (range_subZ_eq_top A hSA z c c' hc hc' hb hb')

omit [CompleteSpace H] in
/-- The first resolvent identity `R_a φ - R_b φ = (a - b) R_a R_b φ`. -/
lemma resolvent_identity (A : H →ₗ.[ℂ] H) (a b : ℂ) (Ra Rb : H →L[ℂ] H)
    (ha : TeschlQM.Shared.IsResolventAt A a Ra) (hb : TeschlQM.Shared.IsResolventAt A b Rb)
    (φ : H) : Ra φ - Rb φ = (a - b) • Ra (Rb φ) := by
  obtain ⟨h, hφ⟩ := hb.1 φ
  have e1 := ha.2 ⟨Rb φ, h⟩
  simp only at e1
  have e2 : (A ⟨Rb φ, h⟩ - a • Rb φ) + (a - b) • Rb φ = φ := by
    refine Eq.trans ?_ hφ
    rw [sub_smul]; abel
  have e3 := congrArg Ra e2
  rw [map_add, e1, map_smul] at e3
  rw [← e3]
  abel

/-- If `A` is symmetric, `R` is its resolvent at a real point `l`, and every real `w < l` lies in
`ρ(A)`, then `R` is a positive operator. -/
lemma resolvent_re_inner_nonneg (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) (l : ℝ)
    (R : H →L[ℂ] H) (hR : TeschlQM.Shared.IsResolventAt A (l : ℂ) R)
    (hρ : ∀ w : ℝ, w < l → (w : ℂ) ∈ TeschlQM.Shared.resolventSet A) (φ : H) :
    0 ≤ (⟪R φ, φ⟫_ℂ).re := by
  have hsa : IsSelfAdjoint R := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    obtain ⟨hx, ex⟩ := hR.1 x
    obtain ⟨hy, ey⟩ := hR.1 y
    show ⟪R x, y⟫_ℂ = ⟪x, R y⟫_ℂ
    calc ⟪R x, y⟫_ℂ = ⟪R x, A ⟨R y, hy⟩ - (l : ℂ) • R y⟫_ℂ := by rw [ey]
      _ = ⟪A ⟨R x, hx⟩ - (l : ℂ) • R x, R y⟫_ℂ := by
          rw [inner_sub_right, inner_sub_left, inner_smul_right, inner_smul_left,
            Complex.conj_ofReal]
          have := hA.2 ⟨R x, hx⟩ ⟨R y, hy⟩
          simp only at this
          rw [this]
      _ = ⟪x, R y⟫_ℂ := by rw [ex]
  have hspec : ∀ x ∈ spectrum ℝ R, 0 ≤ x := by
    intro x hx
    by_contra! hneg
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hneg.ne
    rw [spectrum.mem_iff] at hx
    apply hx
    set w : ℝ := l + x⁻¹ with hw
    obtain ⟨Rw, hRw⟩ := hρ w (by rw [hw]; linarith [inv_lt_zero.mpr hneg])
    have hwl : ((l : ℂ) - (w : ℂ)) = -(x : ℂ)⁻¹ := by rw [hw]; push_cast; ring
    have hlw : ((w : ℂ) - (l : ℂ)) = (x : ℂ)⁻¹ := by rw [hw]; push_cast; ring
    have id1 : ∀ φ : H, R (Rw φ) = (-(x : ℂ)) • (R φ - Rw φ) := by
      intro φ
      rw [resolvent_identity A (l : ℂ) (w : ℂ) R Rw hR hRw φ, hwl, smul_smul]
      field_simp
      simp
    have id2 : ∀ φ : H, Rw (R φ) = (x : ℂ) • (Rw φ - R φ) := by
      intro φ
      rw [resolvent_identity A (w : ℂ) (l : ℂ) Rw R hRw hR φ, hlw, smul_smul]
      field_simp
      simp
    have halg : ∀ φ : H, (algebraMap ℝ (H →L[ℂ] H) x) φ = (x : ℂ) • φ := by
      intro φ
      rw [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, Complex.coe_smul]
    let S : H →L[ℂ] H := (x : ℂ)⁻¹ • (1 : H →L[ℂ] H) + ((x : ℂ)⁻¹ ^ 2) • Rw
    have hS : ∀ φ : H, S φ = (x : ℂ)⁻¹ • φ + ((x : ℂ)⁻¹ ^ 2) • Rw φ := fun φ => rfl
    refine isUnit_iff_exists.mpr ⟨S, ?_, ?_⟩
    · ext φ
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply, halg,
        ContinuousLinearMap.one_apply, hS, map_add, map_smul, map_smul, id1]
      match_scalars <;> field_simp <;> ring
    · ext φ
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply, halg,
        ContinuousLinearMap.one_apply, hS, map_sub, map_smul, id2]
      match_scalars <;> field_simp <;> ring
  have hnn : 0 ≤ R := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) R hsa).mpr hspec
  exact ((ContinuousLinearMap.nonneg_iff_isPositive R).mp hnn).re_inner_nonneg_left φ

end TeschlQM.SelfAdjoint.SpecAux

open TeschlQM.SelfAdjoint TeschlQM.SelfAdjoint.SpecAux in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A) :
    (IsSelfAdjoint A ↔ TeschlQM.Shared.spectrum A ⊆ {z : ℂ | z.im = 0}) ∧
    (∀ E : ℝ, (IsSelfAdjoint A ∧ ∀ ψ : A.domain, E * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re) ↔
      TeschlQM.Shared.spectrum A ⊆ {z : ℂ | z.im = 0 ∧ E ≤ z.re}) ∧
    (IsSelfAdjoint A → ∀ z : ℂ, z.im ≠ 0 → ∀ R : H →L[ℂ] H, TeschlQM.Shared.IsResolventAt A z R →
      ‖R‖ ≤ |z.im|⁻¹) ∧
    (∀ E : ℝ, IsSelfAdjoint A → (∀ ψ : A.domain, E * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re) →
      ∀ l : ℝ, l < E → ∀ R : H →L[ℂ] H, TeschlQM.Shared.IsResolventAt A (l : ℂ) R → ‖R‖ ≤ |l - E|⁻¹) := by
  have resolv_of_im : IsSelfAdjoint A → ∀ z : ℂ, z.im ≠ 0 →
      z ∈ TeschlQM.Shared.resolventSet A := by
    intro hSA z hz
    refine mem_resolventSet A hSA z |z.im| |z.im| (abs_pos.mpr hz) (abs_pos.mpr hz)
      (im_bound A hA z) fun ψ => ?_
    have := im_bound A hA (conj z) ψ
    rwa [Complex.conj_im, abs_neg] at this
  have resolv_of_re : IsSelfAdjoint A → ∀ E : ℝ,
      (∀ ψ : A.domain, E * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re) →
      ∀ l : ℝ, l < E → (l : ℂ) ∈ TeschlQM.Shared.resolventSet A := by
    intro hSA E hE l hl
    refine mem_resolventSet A hSA l (E - l) (E - l) (by linarith) (by linarith)
      (re_bound A E l hE) fun ψ => ?_
    rw [Complex.conj_ofReal]
    exact re_bound A E l hE ψ
  have sa_of_spec : TeschlQM.Shared.spectrum A ⊆ {z : ℂ | z.im = 0} → IsSelfAdjoint A := by
    intro hsub
    have mem : ∀ z : ℂ, z.im ≠ 0 → z ∈ TeschlQM.Shared.resolventSet A := fun z hz => by
      by_contra h
      exact hz (hsub h)
    obtain ⟨R1, hR1⟩ := mem (-Complex.I) (by simp)
    obtain ⟨R2, hR2⟩ := mem Complex.I (by simp)
    refine selfAdjoint_of_range_eq_top A hA Complex.I ?_ ?_
    · rw [eq_top_iff]
      intro φ _
      obtain ⟨h, hφ⟩ := hR1.1 φ
      refine (mem_rangeAdd_iff A _ φ).mpr ⟨⟨R1 φ, h⟩, Eq.trans ?_ hφ⟩
      simp [sub_eq_add_neg]
    · rw [Complex.conj_I, eq_top_iff]
      intro φ _
      obtain ⟨h, hφ⟩ := hR2.1 φ
      refine (mem_rangeAdd_iff A _ φ).mpr ⟨⟨R2 φ, h⟩, Eq.trans ?_ hφ⟩
      simp [sub_eq_add_neg]
  refine ⟨⟨fun hSA z hz => ?_, sa_of_spec⟩, fun E => ⟨?_, ?_⟩, ?_, ?_⟩
  · by_contra him
    exact hz (resolv_of_im hSA z him)
  · rintro ⟨hSA, hE⟩ z hz
    have him : z.im = 0 := by
      by_contra him
      exact hz (resolv_of_im hSA z him)
    refine ⟨him, ?_⟩
    by_contra! hlt
    have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
    rw [hz'] at hz
    exact hz (resolv_of_re hSA E hE z.re hlt)
  · intro hsub
    have hSA := sa_of_spec (fun z hz => (hsub hz).1)
    refine ⟨hSA, fun ψ => ?_⟩
    have key : ∀ l : ℝ, l < E → l * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re := by
      intro l hl
      have hρ : ∀ w : ℝ, w < E → (w : ℂ) ∈ TeschlQM.Shared.resolventSet A := fun w hw => by
        by_contra h
        have := (hsub h).2
        simp only [Complex.ofReal_re] at this
        linarith
      obtain ⟨R, hR⟩ := hρ l hl
      have hpos := resolvent_re_inner_nonneg A hA l R hR (fun w hw => hρ w (by linarith))
        (A ψ - (l : ℂ) • (ψ : H))
      rw [hR.2 ψ, inner_sub_right, inner_smul_right, Complex.sub_re,
        Complex.re_ofReal_mul] at hpos
      have hn : (⟪(ψ : H), (ψ : H)⟫_ℂ).re = ‖(ψ : H)‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
      rw [hn] at hpos
      linarith
    have ht : Tendsto (fun l : ℝ => l * ‖(ψ : H)‖ ^ 2) (𝓝[<] E) (𝓝 (E * ‖(ψ : H)‖ ^ 2)) :=
      ((continuous_id.mul continuous_const).tendsto E).mono_left nhdsWithin_le_nhds
    exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun l hl => key l hl)
  · intro hSA z hz R hR
    exact norm_resolvent_le A z |z.im| (abs_pos.mpr hz) (im_bound A hA z) R hR
  · intro E hSA hE l hl R hR
    have := norm_resolvent_le A l (E - l) (by linarith) (re_bound A E l hE) R hR
    rwa [abs_sub_comm, abs_of_pos (by linarith)]
