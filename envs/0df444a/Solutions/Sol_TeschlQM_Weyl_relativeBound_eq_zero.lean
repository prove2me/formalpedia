-- Prove2me | solution 1 for TeschlQM.Weyl.relativeBound_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T09:19:02.743952+00:00
-- url     : https://prove2.me/submissions/400d4882-4ae7-4c44-9143-6e68a09eec8c

-- Research directed by Alexander Richard Towell (queelius); Lean proof by OpenAI Codex.
-- Mathematical source: Gerald Teschl, Mathematical Methods in Quantum Mechanics (2009), Lemma 6.22.
-- Platform formulation/definitions: mikedeng1; statement review: Shuze Chen.
-- Lean and Mathlib contributors supplied the formal foundations.
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_IsRelativelyCompact
import Definitions.Def_TeschlQM_Shared_relativeBound
import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter Set
open scoped Topology ComplexConjugate
namespace CompactResearch
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma weak_zero (R : H →L[ℂ] H) (hR : Function.Injective R) (u : ℕ → H)
    (hu : ∀ n, ‖u n‖ ≤ 1) (hRu : Tendsto (fun n => R (u n)) atTop (𝓝 0)) (v : H) :
    Tendsto (fun n => inner ℂ v (u n)) atTop (𝓝 0) := by
  have hk : R.ker = ⊥ := LinearMap.ker_eq_bot.mpr hR
  have hd : R.adjoint.range.topologicalClosure = ⊤ := by
    rw [← R.orthogonal_ker,hk,Submodule.bot_orthogonal_eq_top]
  have hv : v ∈ closure (Set.range R.adjoint) := by
    change v ∈ R.adjoint.range.topologicalClosure
    rw [hd];trivial
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨w,⟨y,rfl⟩,hy⟩ := Metric.mem_closure_iff.mp hv (ε/2) (by linarith)
  have hy' : ‖v-R.adjoint y‖ < ε/2 := by simpa [dist_eq_norm,norm_sub_rev] using hy
  have ht : Tendsto (fun n => inner ℂ y (R (u n))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.inner hRu
  have he := Metric.tendsto_nhds.mp ht (ε/2) (by linarith)
  filter_upwards [he] with n hn
  rw [dist_zero_right] at hn ⊢
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (v-R.adjoint y) (u n)
  have h2 := mul_le_mul_of_nonneg_left (hu n) (norm_nonneg (v-R.adjoint y))
  have heq : inner ℂ v (u n) = inner ℂ (v-R.adjoint y) (u n)+inner ℂ y (R (u n)) := by
    rw [inner_sub_left,R.adjoint_inner_left];ring
  rw [heq]
  exact (norm_add_le _ _).trans_lt (by nlinarith)
lemma compact_estimate (R C : H →L[ℂ] H) (hR : Function.Injective R)
    (hC : IsCompactOperator C) (ε : ℝ) (hε : 0 < ε) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ x : H, ‖C x‖ ≤ ε*‖x‖+b*‖R x‖ := by
  classical
  by_contra h
  push_neg at h
  have hex (n : ℕ) : ∃ u : H, ‖u‖ = 1 ∧ ε < ‖C u‖ ∧ ‖R u‖ ≤ ‖C‖/((n:ℝ)+1) := by
    obtain ⟨x,hx⟩ := h ((n:ℝ)+1) (by positivity)
    have hx0 : x ≠ 0 := by intro hz;subst x;simp at hx
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    let u : H := (‖x‖⁻¹ : ℂ) • x
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hx0
    have hCu : ‖C u‖ = ‖C x‖/‖x‖ := by simp [u,map_smul,norm_smul,Complex.norm_real,abs_of_nonneg (inv_nonneg.mpr hn.le),div_eq_mul_inv,mul_comm]
    have hRu : ‖R u‖ = ‖R x‖/‖x‖ := by simp [u,map_smul,norm_smul,Complex.norm_real,abs_of_nonneg (inv_nonneg.mpr hn.le),div_eq_mul_inv,mul_comm]
    have hineq : ε+((n:ℝ)+1)*‖R u‖ < ‖C u‖ := by
      rw [hCu,hRu]
      apply (lt_div_iff₀ hn).mpr
      field_simp [ne_of_gt hn]
      nlinarith
    have hCb : ‖C u‖ ≤ ‖C‖ := by simpa [hu] using C.le_opNorm u
    refine ⟨u,hu,?_,?_⟩
    · have hnn := mul_nonneg (show 0 ≤ (n:ℝ)+1 by positivity) (norm_nonneg (R u));linarith
    · apply (le_div_iff₀ (show 0 < (n:ℝ)+1 by positivity)).mpr
      nlinarith
  choose u hu hCu hRu using hex
  have ht : Tendsto (fun n : ℕ => ‖C‖/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hRlim : Tendsto (fun n => R (u n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) hRu ht
  obtain ⟨K,hK,hsub⟩ := hC.image_closedBall_subset_compact (f := C.toLinearMap) 1
  have hmem (n : ℕ) : C (u n) ∈ K := hsub ⟨u n,by simpa [Metric.mem_closedBall,dist_zero_right,hu],rfl⟩
  obtain ⟨y,hy,φ,hφ,hlim⟩ := hK.tendsto_subseq hmem
  have hweak := (weak_zero R hR u (fun n => (hu n).le) hRlim (C.adjoint y)).comp hφ.tendsto_atTop
  have hinner : Tendsto (fun n => inner ℂ y (C (u (φ n)))) atTop (𝓝 (inner ℂ y y)) :=
    tendsto_const_nhds.inner hlim
  have hzero : inner ℂ y y = 0 := by
    have hweak' : Tendsto (fun n => inner ℂ y (C (u (φ n)))) atTop (𝓝 0) := by
      simpa only [Function.comp_def,C.adjoint_inner_left] using hweak
    exact tendsto_nhds_unique hinner hweak'
  have hy0 : y = 0 := inner_self_eq_zero.mp hzero
  have hlo : ε ≤ ‖y‖ := le_of_tendsto_of_tendsto tendsto_const_nhds hlim.norm (Filter.Eventually.of_forall fun n => (hCu (φ n)).le)
  simp [hy0] at hlo
  exact (not_le_of_gt hε) hlo
end CompactResearch
namespace CompactResearch
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open TeschlQM.Shared
lemma resolvent_injective (A : H →ₗ.[ℂ] H) (z : ℂ) (R : H →L[ℂ] H)
    (hR : IsResolventAt A z R) : Function.Injective R := by
  intro x y hxy
  obtain ⟨hx,hex⟩ := hR.1 x
  obtain ⟨hy,hey⟩ := hR.1 y
  have ha : A ⟨R x,hx⟩ = A ⟨R y,hy⟩ := congrArg A (Subtype.ext hxy)
  rw [← hex,← hey,ha,hxy]
lemma relative_estimate (A K : H →ₗ.[ℂ] H) (hK : IsRelativelyCompact K A)
    (ε : ℝ) (hε : 0 < ε) : ∃ b : ℝ, IsRelativelyBoundedWith A K ε b := by
  obtain ⟨z,R,hR,C,hC,hKR⟩ := hK
  obtain ⟨b,hb,hbound⟩ := compact_estimate R C (resolvent_injective A z R hR) hC ε hε
  have hdom : A.domain ≤ K.domain := by
    intro ψ hψ
    obtain ⟨h,_⟩ := hKR (A ⟨ψ,hψ⟩-z • ψ)
    simpa only [hR.2 ⟨ψ,hψ⟩] using h
  refine ⟨ε*‖z‖+b,hdom,hε.le,by positivity,?_⟩
  intro ψ hA hK
  let φ := A ⟨ψ,hA⟩-z • ψ
  have hRφ : R φ = ψ := hR.2 ⟨ψ,hA⟩
  obtain ⟨hK',hCφ⟩ := hKR φ
  have he : C φ = K ⟨ψ,hK⟩ := by
    rw [← hCφ]
    exact congrArg K (Subtype.ext hRφ)
  have hbnd := hbound φ
  rw [hRφ,he] at hbnd
  have hn : ‖φ‖ ≤ ‖A ⟨ψ,hA⟩‖+‖z‖*‖ψ‖ := by
    exact (norm_sub_le _ _).trans (by rw [norm_smul])
  nlinarith [mul_le_mul_of_nonneg_left hn hε.le]
lemma relative_zero (A K : H →ₗ.[ℂ] H) (hK : IsRelativelyCompact K A) : relativeBound A K = 0 := by
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have he : (0:ℝ) < ε := by exact_mod_cast hε
  obtain ⟨b,hb⟩ := relative_estimate A K hK ε he
  have hle : relativeBound A K ≤ ENNReal.ofReal ε :=
    iInf_le_of_le (ε:ℝ) (iInf_le_of_le (⟨b,hb⟩ : ∃ b : ℝ, IsRelativelyBoundedWith A K ε b) le_rfl)
  simpa using hle
end CompactResearch


/-- Teschl, Lemma 6.22, p. 148. Let `A` be self-adjoint and suppose `K` is relatively compact with
respect to `A`. Then the `A`-bound of `K` is zero. (The `A`-bound is valued in `[0, ∞]` and is `∞`
for an operator that is not `A` bounded, so the conclusion includes that `K` is `A` bounded.) -/
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A K : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hK : TeschlQM.Shared.IsRelativelyCompact K A) :
    TeschlQM.Shared.relativeBound A K = 0 := by
  exact CompactResearch.relative_zero A K hK


