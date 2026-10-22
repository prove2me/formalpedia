-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P17.finite_kraus_matrix
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T20:23:26.80012+00:00
-- url     : https://prove2.me/submissions/26330f5a-15bf-4066-b764-d863db24afba

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

open QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

section g72gk34
variable {A : Type*} [CStarAlgebra A] {H : SeparableHilbertSpace} {K : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def g72gk34_Phi (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K) :
    ((A × H) →₀ ℂ) →ₗ[ℂ] K :=
  Finsupp.linearCombination ℂ (fun p : A × H => pi p.1 (V p.2))

def g72gk34_s (R : A →ₗ[ℂ] HilbertEndomorphism H) (f g : (A × H) →₀ ℂ) : ℂ :=
  f.sum fun p c => g.sum fun q d => conj c * d * inner ℂ p.2 (R (star p.1 * q.1) q.2)

lemma g72gk34_s_add_left (R : A →ₗ[ℂ] HilbertEndomorphism H) (f f' g : (A × H) →₀ ℂ) :
    g72gk34_s R (f + f') g = g72gk34_s R f g + g72gk34_s R f' g := by
  unfold g72gk34_s
  apply Finsupp.sum_add_index'
  · intro p; simp [Finsupp.sum]
  · intro p c c'; simp [Finsupp.sum, add_mul, Finset.sum_add_distrib]

lemma g72gk34_s_smul_left (R : A →ₗ[ℂ] HilbertEndomorphism H) (c : ℂ) (f g : (A × H) →₀ ℂ) :
    g72gk34_s R (c • f) g = conj c * g72gk34_s R f g := by
  unfold g72gk34_s
  rw [Finsupp.sum_smul_index']
  · simp only [Finsupp.sum, Finset.mul_sum, smul_eq_mul, map_mul]
    apply Finset.sum_congr rfl; intro p _; apply Finset.sum_congr rfl; intro q _; ring
  · intro p; simp [Finsupp.sum]

lemma g72gk34_s_add_right (R : A →ₗ[ℂ] HilbertEndomorphism H) (f g g' : (A × H) →₀ ℂ) :
    g72gk34_s R f (g + g') = g72gk34_s R f g + g72gk34_s R f g' := by
  unfold g72gk34_s
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr; intro p _
  apply Finsupp.sum_add_index'
  · intro q; simp
  · intro q d d'; ring

lemma g72gk34_s_smul_right (R : A →ₗ[ℂ] HilbertEndomorphism H) (c : ℂ) (f g : (A × H) →₀ ℂ) :
    g72gk34_s R f (c • g) = c * g72gk34_s R f g := by
  unfold g72gk34_s
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr; intro p _
  rw [Finsupp.sum_smul_index', Finsupp.mul_sum]
  · apply Finsupp.sum_congr; intro q _; simp only [smul_eq_mul]; ring
  · intro q; simp

lemma g72gk34_gram (R : A →ₗ[ℂ] HilbertEndomorphism H) (hR : GramCompletelyPositive R)
    (f : (A × H) →₀ ℂ) : (g72gk34_s R f f).im = 0 ∧ 0 ≤ (g72gk34_s R f f).re := by
  set e := f.support.equivFin
  have key := hR f.support.card (fun i => f (e.symm i).1 • (e.symm i).1.1) (fun i => (e.symm i).1.2)
  have hz : (∑ i, ∑ j, inner ℂ ((fun i => (e.symm i).1.2) i)
      (R (star ((fun i => f (e.symm i).1 • (e.symm i).1.1) i) *
        (fun i => f (e.symm i).1 • (e.symm i).1.1) j) ((fun i => (e.symm i).1.2) j))) =
      g72gk34_s R f f := by
    unfold g72gk34_s Finsupp.sum
    rw [← Finset.sum_coe_sort f.support, ← e.symm.sum_comp]
    apply Finset.sum_congr rfl; intro i _
    beta_reduce
    rw [← Finset.sum_coe_sort f.support, ← e.symm.sum_comp]
    apply Finset.sum_congr rfl; intro j _
    simp only [star_smul, smul_mul_smul_comm, map_smul, ContinuousLinearMap.smul_apply,
      inner_smul_right, Complex.star_def]
  simp only at key
  rw [hz] at key
  exact key

lemma g72gk34_herm (R : A →ₗ[ℂ] HilbertEndomorphism H) (hR : GramCompletelyPositive R)
    (f g : (A × H) →₀ ℂ) : g72gk34_s R g f = conj (g72gk34_s R f g) := by
  have h1 := (g72gk34_gram R hR (f + g)).1
  have h2 := (g72gk34_gram R hR (f + Complex.I • g)).1
  have hf := (g72gk34_gram R hR f).1
  have hg := (g72gk34_gram R hR g).1
  have e1 : g72gk34_s R (f + g) (f + g) = g72gk34_s R f f + g72gk34_s R f g +
      g72gk34_s R g f + g72gk34_s R g g := by
    rw [g72gk34_s_add_left, g72gk34_s_add_right, g72gk34_s_add_right]; ring
  have e2 : g72gk34_s R (f + Complex.I • g) (f + Complex.I • g) = g72gk34_s R f f +
      Complex.I * g72gk34_s R f g - Complex.I * g72gk34_s R g f + g72gk34_s R g g := by
    rw [g72gk34_s_add_left, g72gk34_s_add_right, g72gk34_s_add_right, g72gk34_s_smul_left,
      g72gk34_s_smul_left, g72gk34_s_smul_right, g72gk34_s_smul_right, Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]; ring
  rw [e1] at h1
  rw [e2] at h2
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, zero_add] at h1 h2
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith

def g72gk34_core (R : A →ₗ[ℂ] HilbertEndomorphism H) (hR : GramCompletelyPositive R) :
    PreInnerProductSpace.Core ℂ ((A × H) →₀ ℂ) where
  inner f g := g72gk34_s R f g
  conj_inner_symm x y := (g72gk34_herm R hR x y).symm ▸ by simp
  re_inner_nonneg x := (g72gk34_gram R hR x).2
  add_left x y z := g72gk34_s_add_left R x y z
  smul_left x y r := g72gk34_s_smul_left R r x y

lemma g72gk34_cs (R : A →ₗ[ℂ] HilbertEndomorphism H) (hR : GramCompletelyPositive R)
    (f g : (A × H) →₀ ℂ) :
    ‖g72gk34_s R f g‖ ^ 2 ≤ (g72gk34_s R f f).re * (g72gk34_s R g g).re := by
  letI := g72gk34_core R hR
  have := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) f g
  have e : ‖g72gk34_s R g f‖ = ‖g72gk34_s R f g‖ := by
    rw [g72gk34_herm R hR f g, Complex.norm_conj]
  change ‖g72gk34_s R f g‖ * ‖g72gk34_s R g f‖ ≤
    (g72gk34_s R f f).re * (g72gk34_s R g g).re at this
  rw [e] at this
  rw [sq]; exact this

lemma g72gk34_sT (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K)
    (T : A →ₗ[ℂ] HilbertEndomorphism H) (hdil : ∀ a, T a = compress V (pi a))
    (f g : (A × H) →₀ ℂ) :
    g72gk34_s T f g = inner ℂ (g72gk34_Phi pi V f) (g72gk34_Phi pi V g) := by
  unfold g72gk34_s g72gk34_Phi
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro q _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [hdil, compress, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, map_mul, map_star, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  ring

lemma g72gk34_ssum {I : Type*} [Fintype I] (Ti : I → A →ₗ[ℂ] HilbertEndomorphism H)
    (f g : (A × H) →₀ ℂ) :
    g72gk34_s (∑ i, Ti i) f g = ∑ i, g72gk34_s (Ti i) f g := by
  unfold g72gk34_s
  simp only [Finsupp.sum, LinearMap.sum_apply, ContinuousLinearMap.sum_apply, inner_sum,
    Finset.mul_sum]
  exact (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans Finset.sum_comm

lemma g72gk34_dense (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K)
    (hmin : (Submodule.span ℂ {z : K | ∃ a : A, ∃ eta : H, z = pi a (V eta)}).topologicalClosure = ⊤) :
    DenseRange (g72gk34_Phi pi V) := by
  have h1 : LinearMap.range (g72gk34_Phi pi V) =
      Submodule.span ℂ {z : K | ∃ a : A, ∃ eta : H, z = pi a (V eta)} := by
    rw [g72gk34_Phi, Finsupp.range_linearCombination]
    congr 1
    ext z
    constructor
    · rintro ⟨⟨a, eta⟩, rfl⟩; exact ⟨a, eta, rfl⟩
    · rintro ⟨a, eta, rfl⟩; exact ⟨⟨a, eta⟩, rfl⟩
  have h2 : Dense (LinearMap.range (g72gk34_Phi pi V) : Set K) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, h1]
    exact hmin
  intro x
  have := h2 x
  simpa [LinearMap.coe_range] using this

lemma g72gk34_ext (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K)
    (hd : DenseRange (g72gk34_Phi pi V)) (P Q : HilbertEndomorphism K)
    (h : ∀ f g, inner ℂ (g72gk34_Phi pi V f) (P (g72gk34_Phi pi V g)) =
      inner ℂ (g72gk34_Phi pi V f) (Q (g72gk34_Phi pi V g))) : P = Q := by
  have h1 : ∀ g, P (g72gk34_Phi pi V g) = Q (g72gk34_Phi pi V g) := by
    intro g
    rw [← sub_eq_zero]
    set z := P (g72gk34_Phi pi V g) - Q (g72gk34_Phi pi V g)
    have hz : ∀ w, inner ℂ w z = 0 := by
      intro w
      refine hd.induction_on w (isClosed_eq (continuous_id.inner continuous_const)
        continuous_const) (fun f => ?_)
      rw [inner_sub_right, h f g, sub_self]
    exact inner_self_eq_zero.mp (hz z)
  ext x
  exact hd.induction_on x (isClosed_eq P.continuous Q.continuous) h1

def g72gk34_M (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K)
    (R : A →ₗ[ℂ] HilbertEndomorphism H) (hd : DenseRange (g72gk34_Phi pi V))
    (hb : ∀ f g, ‖g72gk34_s R f g‖ ≤ ‖g72gk34_Phi pi V g‖ * ‖g72gk34_Phi pi V f‖) :
    ((A × H) →₀ ℂ) →ₗ[ℂ] (K →L⋆[ℂ] ℂ) :=
  let ℓ : ((A × H) →₀ ℂ) → (((A × H) →₀ ℂ) →ₛₗ[starRingEnd ℂ] ℂ) := fun g =>
    { toFun := fun f => g72gk34_s R f g
      map_add' := fun f f' => g72gk34_s_add_left R f f' g
      map_smul' := fun c f => by simp [g72gk34_s_smul_left] }
  { toFun := fun g => (ℓ g).extendOfNorm (g72gk34_Phi pi V)
    map_add' := fun g g' => by
      apply LinearMap.extendOfNorm_unique hd (‖g72gk34_Phi pi V (g + g')‖)
        (fun f => hb f (g + g'))
      refine LinearMap.ext fun f => ?_
      simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
        ContinuousLinearMap.add_apply]
      rw [LinearMap.extendOfNorm_eq hd ⟨_, fun f => hb f g⟩,
        LinearMap.extendOfNorm_eq hd ⟨_, fun f => hb f g'⟩]
      exact (g72gk34_s_add_right R f g g').symm
    map_smul' := fun c g => by
      apply LinearMap.extendOfNorm_unique hd (‖g72gk34_Phi pi V (c • g)‖)
        (fun f => hb f (c • g))
      refine LinearMap.ext fun f => ?_
      simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
        ContinuousLinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
      rw [LinearMap.extendOfNorm_eq hd ⟨_, fun f => hb f g⟩]
      exact (g72gk34_s_smul_right R c f g).symm }

lemma g72gk34_M_apply (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K)
    (R : A →ₗ[ℂ] HilbertEndomorphism H) (hd : DenseRange (g72gk34_Phi pi V))
    (hb : ∀ f g, ‖g72gk34_s R f g‖ ≤ ‖g72gk34_Phi pi V g‖ * ‖g72gk34_Phi pi V f‖)
    (f g : (A × H) →₀ ℂ) :
    g72gk34_M pi V R hd hb g (g72gk34_Phi pi V f) = g72gk34_s R f g :=
  LinearMap.extendOfNorm_eq hd ⟨_, fun f => hb f g⟩ f

lemma g72gk34_M_bd (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K)
    (R : A →ₗ[ℂ] HilbertEndomorphism H) (hd : DenseRange (g72gk34_Phi pi V))
    (hb : ∀ f g, ‖g72gk34_s R f g‖ ≤ ‖g72gk34_Phi pi V g‖ * ‖g72gk34_Phi pi V f‖)
    (g : (A × H) →₀ ℂ) :
    ‖g72gk34_M pi V R hd hb g‖ ≤ 1 * ‖g72gk34_Phi pi V g‖ := by
  rw [one_mul]
  exact LinearMap.opNorm_extendOfNorm_le hd (norm_nonneg _) (fun f => hb f g)

def g72gk34_G (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K)
    (R : A →ₗ[ℂ] HilbertEndomorphism H) (hd : DenseRange (g72gk34_Phi pi V))
    (hb : ∀ f g, ‖g72gk34_s R f g‖ ≤ ‖g72gk34_Phi pi V g‖ * ‖g72gk34_Phi pi V f‖) :
    HilbertEndomorphism K :=
  InnerProductSpace.continuousLinearMapOfBilin
    ((g72gk34_M pi V R hd hb).extendOfNorm (g72gk34_Phi pi V)).flip

lemma g72gk34_G_spec (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K)
    (R : A →ₗ[ℂ] HilbertEndomorphism H) (hd : DenseRange (g72gk34_Phi pi V))
    (hb : ∀ f g, ‖g72gk34_s R f g‖ ≤ ‖g72gk34_Phi pi V g‖ * ‖g72gk34_Phi pi V f‖)
    (f g : (A × H) →₀ ℂ) :
    inner ℂ (g72gk34_G pi V R hd hb (g72gk34_Phi pi V f)) (g72gk34_Phi pi V g) =
      g72gk34_s R f g := by
  rw [g72gk34_G, InnerProductSpace.continuousLinearMapOfBilin_apply,
    ContinuousLinearMap.flip_apply,
    LinearMap.extendOfNorm_eq hd ⟨1, fun g => g72gk34_M_bd pi V R hd hb g⟩,
    g72gk34_M_apply]


def g72gk34_ma (a : A) (f : (A × H) →₀ ℂ) : (A × H) →₀ ℂ :=
  Finsupp.mapDomain (fun p : A × H => (a * p.1, p.2)) f

lemma g72gk34_Phi_ma (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K) (a : A)
    (f : (A × H) →₀ ℂ) : g72gk34_Phi pi V (g72gk34_ma a f) = pi a (g72gk34_Phi pi V f) := by
  rw [g72gk34_Phi, g72gk34_ma, Finsupp.linearCombination_mapDomain]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, Function.comp_apply,
    map_mul, ContinuousLinearMap.mul_apply]

lemma g72gk34_s_ma (R : A →ₗ[ℂ] HilbertEndomorphism H) (a : A) (f g : (A × H) →₀ ℂ) :
    g72gk34_s R (g72gk34_ma (star a) f) g = g72gk34_s R f (g72gk34_ma a g) := by
  unfold g72gk34_s g72gk34_ma
  rw [Finsupp.sum_mapDomain_index]
  · apply Finsupp.sum_congr; intro p _
    rw [Finsupp.sum_mapDomain_index]
    · apply Finsupp.sum_congr; intro q _
      simp only [star_mul, star_star, mul_assoc]
    · intro q; simp
    · intro q d d'; ring
  · intro p; simp [Finsupp.sum]
  · intro p c c'; simp [Finsupp.sum, add_mul, Finset.sum_add_distrib]

lemma g72gk34_Q (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K)
    (R : A →ₗ[ℂ] HilbertEndomorphism H) (Y : HilbertEndomorphism K)
    (hY : ∀ a, (pi a).comp Y = Y.comp (pi a)) (hR : ∀ a, R a = compress V ((pi a).comp Y))
    (f g : (A × H) →₀ ℂ) :
    inner ℂ (g72gk34_Phi pi V f) (Y (g72gk34_Phi pi V g)) = g72gk34_s R f g := by
  unfold g72gk34_s g72gk34_Phi
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro q _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro p _
  have hc := congrArg (fun F : HilbertEndomorphism K => F (V q.2)) (hY q.1)
  simp only [ContinuousLinearMap.comp_apply] at hc
  rw [hR, compress, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, map_mul, map_star,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, hc]
  ring

end g72gk34

theorem g72gk34_rn {A : Type*} [CStarAlgebra A] {H : SeparableHilbertSpace} {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : A →ₗ[ℂ] HilbertEndomorphism H) (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K)
    (h_dilation : ∀ a, T a = compress V (pi a))
    (h_minimal : (Submodule.span ℂ {z : K | ∃ a : A, ∃ eta : H, z = pi a (V eta)}).topologicalClosure = ⊤)
    (I : Type*) [Fintype I]
    (Ti : I → A →ₗ[ℂ] HilbertEndomorphism H) (hgram : ∀ i, GramCompletelyPositive (Ti i))
    (h_sum : T = ∑ i, Ti i) :
    ∃! F : I → HilbertEndomorphism K,
      (∀ i, (F i).IsPositive ∧ ∀ a, (pi a).comp (F i) = (F i).comp (pi a)) ∧
      (∑ i, F i) = ContinuousLinearMap.id ℂ K ∧
      ∀ i a, Ti i a = compress V ((pi a).comp (F i)) := by
  have hd := g72gk34_dense pi V h_minimal
  have hTeq : ∀ f g, ∑ i, g72gk34_s (Ti i) f g =
      inner ℂ (g72gk34_Phi pi V f) (g72gk34_Phi pi V g) := by
    intro f g
    rw [← g72gk34_ssum, ← h_sum, g72gk34_sT pi V T h_dilation]
  have hle : ∀ i f, (g72gk34_s (Ti i) f f).re ≤ ‖g72gk34_Phi pi V f‖ ^ 2 := by
    intro i f
    have h1 := congrArg Complex.re (hTeq f f)
    rw [Complex.re_sum] at h1
    have h3 : (g72gk34_s (Ti i) f f).re ≤ ∑ j, (g72gk34_s (Ti j) f f).re :=
      Finset.single_le_sum (f := fun j => (g72gk34_s (Ti j) f f).re)
        (fun j _ => (g72gk34_gram _ (hgram j) f).2) (Finset.mem_univ i)
    have h4 : (inner ℂ (g72gk34_Phi pi V f) (g72gk34_Phi pi V f)).re =
        ‖g72gk34_Phi pi V f‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
    linarith
  have hb : ∀ i f g, ‖g72gk34_s (Ti i) f g‖ ≤
      ‖g72gk34_Phi pi V g‖ * ‖g72gk34_Phi pi V f‖ := by
    intro i f g
    have hcs := g72gk34_cs (Ti i) (hgram i) f g
    have h0f := (g72gk34_gram _ (hgram i) f).2
    have h0g := (g72gk34_gram _ (hgram i) g).2
    have hm := mul_le_mul (hle i f) (hle i g) h0g (sq_nonneg _)
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
    nlinarith
  set F : I → HilbertEndomorphism K := fun i => g72gk34_G pi V (Ti i) hd (hb i) with hFdef
  have spec : ∀ i f g, inner ℂ (F i (g72gk34_Phi pi V f)) (g72gk34_Phi pi V g) =
      g72gk34_s (Ti i) f g := fun i f g => g72gk34_G_spec pi V (Ti i) hd (hb i) f g
  have spec' : ∀ i f g, inner ℂ (g72gk34_Phi pi V f) (F i (g72gk34_Phi pi V g)) =
      g72gk34_s (Ti i) f g := by
    intro i f g
    rw [← inner_conj_symm, spec, g72gk34_herm _ (hgram i) f g, Complex.conj_conj]
  have hsa : ∀ i, IsSelfAdjoint (F i) := by
    intro i
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    apply g72gk34_ext pi V hd
    intro f g
    rw [ContinuousLinearMap.adjoint_inner_right, spec, spec']
  have hcomm : ∀ i, ∀ a, (pi a).comp (F i) = (F i).comp (pi a) := by
    intro i a
    apply g72gk34_ext pi V hd
    intro f g
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      ← map_star, ← g72gk34_Phi_ma, ← g72gk34_Phi_ma, spec', spec', g72gk34_s_ma]
  have hpos : ∀ i, (F i).IsPositive := by
    intro i
    rw [ContinuousLinearMap.isPositive_def']
    refine ⟨hsa i, fun x => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    refine hd.induction_on x (isClosed_le continuous_const ?_) (fun f => ?_)
    · exact Complex.continuous_re.comp (((F i).continuous).inner continuous_id)
    · rw [spec]; exact (g72gk34_gram _ (hgram i) f).2
  have hsum : (∑ i, F i) = ContinuousLinearMap.id ℂ K := by
    apply g72gk34_ext pi V hd
    intro f g
    rw [ContinuousLinearMap.sum_apply, inner_sum, ContinuousLinearMap.id_apply, ← hTeq]
    exact Finset.sum_congr rfl fun i _ => spec' i f g
  have hcomp : ∀ i a, Ti i a = compress V ((pi a).comp (F i)) := by
    intro i a
    ext eta
    apply ext_inner_left ℂ
    intro xi
    have e1 : g72gk34_s (Ti i) (Finsupp.single ((1 : A), xi) 1) (Finsupp.single (a, eta) 1) =
        inner ℂ xi (Ti i a eta) := by
      simp [g72gk34_s, Finsupp.sum_single_index]
    have e2 := spec' i (Finsupp.single ((1 : A), xi) 1) (Finsupp.single (a, eta) 1)
    simp only [g72gk34_Phi, Finsupp.linearCombination_single, one_smul, map_one,
      ContinuousLinearMap.one_apply] at e2
    rw [← e1, ← e2, compress, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    have hc := congrArg (fun X : HilbertEndomorphism K => X (V eta)) (hcomm i a)
    simp only [ContinuousLinearMap.comp_apply] at hc
    rw [hc]
  refine ⟨F, ⟨fun i => ⟨hpos i, hcomm i⟩, hsum, hcomp⟩, ?_⟩
  rintro Y ⟨hY1, _, hY3⟩
  funext i
  apply g72gk34_ext pi V hd
  intro f g
  rw [g72gk34_Q pi V (Ti i) (Y i) (hY1 i).2 (hY3 i), spec']

section g72gk34t
variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma g72gk34_tdense :
    DenseRange (UniformSpace.Completion.toComplL : H ⊗[ℂ] E →L[ℂ] NoiseSpace H E) := by
  simpa using UniformSpace.Completion.denseRange_coe

lemma g72gk34_tunif :
    IsUniformInducing (UniformSpace.Completion.toComplL : H ⊗[ℂ] E →L[ℂ] NoiseSpace H E) := by
  simpa using UniformSpace.Completion.isUniformInducing_coe (H ⊗[ℂ] E)

lemma g72gk34_ctm_coe (A : H →L[ℂ] H) (B : E →L[ℂ] E) (x : H ⊗[ℂ] E) :
    completedTensorMap A B (x : NoiseSpace H E) =
      ((TensorProduct.mapL A B x : H ⊗[ℂ] E) : NoiseSpace H E) := by
  have := ContinuousLinearMap.extend_eq
    ((UniformSpace.Completion.toComplL : H ⊗[ℂ] E →L[ℂ] NoiseSpace H E).comp
      (TensorProduct.mapL A B)) g72gk34_tdense g72gk34_tunif x
  simpa [completedTensorMap] using this

lemma g72gk34_text {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (u v : NoiseSpace H E →L[ℂ] F) (h : ∀ x : H ⊗[ℂ] E, u (x : NoiseSpace H E) = v x) :
    u = v := by
  ext z
  refine UniformSpace.Completion.induction_on z ?_ h
  exact isClosed_eq u.continuous v.continuous

lemma g72gk34_ctm_comp (A C : H →L[ℂ] H) (B D : E →L[ℂ] E) :
    (completedTensorMap A B).comp (completedTensorMap C D) =
      completedTensorMap (A.comp C) (B.comp D) := by
  apply g72gk34_text; intro x
  rw [ContinuousLinearMap.comp_apply, g72gk34_ctm_coe, g72gk34_ctm_coe, g72gk34_ctm_coe,
    TensorProduct.mapL_comp, ContinuousLinearMap.comp_apply]

lemma g72gk34_ctm_add_left (A A' : H →L[ℂ] H) (B : E →L[ℂ] E) :
    completedTensorMap (A + A') B = completedTensorMap A B + completedTensorMap A' B := by
  apply g72gk34_text; intro x
  rw [ContinuousLinearMap.add_apply, g72gk34_ctm_coe, g72gk34_ctm_coe, g72gk34_ctm_coe,
    TensorProduct.mapL_add_left, ContinuousLinearMap.add_apply, UniformSpace.Completion.coe_add]

lemma g72gk34_ctm_smul_left (c : ℂ) (A : H →L[ℂ] H) (B : E →L[ℂ] E) :
    completedTensorMap (c • A) B = c • completedTensorMap A B := by
  apply g72gk34_text; intro x
  rw [ContinuousLinearMap.smul_apply, g72gk34_ctm_coe, g72gk34_ctm_coe,
    TensorProduct.mapL_smul_left, ContinuousLinearMap.smul_apply, UniformSpace.Completion.coe_smul]

lemma g72gk34_ctm_sub_right (A : H →L[ℂ] H) (B B' : E →L[ℂ] E) :
    completedTensorMap A (B - B') = completedTensorMap A B - completedTensorMap A B' := by
  apply g72gk34_text; intro x
  have hm : TensorProduct.mapL A (B - B') = TensorProduct.mapL A B - TensorProduct.mapL A B' := by
    rw [sub_eq_add_neg, TensorProduct.mapL_add_right, ← neg_one_smul ℂ B',
      TensorProduct.mapL_smul_right]
    rw [sub_eq_add_neg]
    congr 1
    exact neg_one_smul ℂ (TensorProduct.mapL A B')
  rw [ContinuousLinearMap.sub_apply, g72gk34_ctm_coe, g72gk34_ctm_coe, g72gk34_ctm_coe, hm,
    ContinuousLinearMap.sub_apply, UniformSpace.Completion.coe_sub]

lemma g72gk34_ctm_zero_left (B : E →L[ℂ] E) :
    completedTensorMap (0 : H →L[ℂ] H) B = 0 := by
  apply g72gk34_text; intro x
  rw [g72gk34_ctm_coe, TensorProduct.mapL_zero_left, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.zero_apply, UniformSpace.Completion.coe_zero]

lemma g72gk34_ctm_id :
    completedTensorMap (ContinuousLinearMap.id ℂ H) (ContinuousLinearMap.id ℂ E) =
      ContinuousLinearMap.id ℂ _ := by
  apply g72gk34_text; intro x
  rw [g72gk34_ctm_coe, TensorProduct.mapL_id_id]; rfl

lemma g72gk34_inner_ctm (A : H →L[ℂ] H) (B : E →L[ℂ] E) (x y : NoiseSpace H E) :
    inner ℂ (completedTensorMap A B x) y =
      inner ℂ x (completedTensorMap (ContinuousLinearMap.adjoint A)
        (ContinuousLinearMap.adjoint B) y) := by
  have h0 : ∀ a b : H ⊗[ℂ] E, inner ℂ (TensorProduct.mapL A B a) b =
      inner ℂ a (TensorProduct.mapL (ContinuousLinearMap.adjoint A)
        (ContinuousLinearMap.adjoint B) b) := by
    intro a b
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul h e =>
      induction b using TensorProduct.induction_on with
      | zero => simp
      | tmul h' e' =>
        simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
          ContinuousLinearMap.adjoint_inner_right]
      | add b b' hb hb' => simp only [map_add, inner_add_right, hb, hb']
    | add a a' ha ha' => simp only [map_add, inner_add_left, ha, ha']
  refine UniformSpace.Completion.induction_on x (isClosed_eq ?_ ?_) (fun a => ?_)
  · exact (completedTensorMap A B).continuous.inner continuous_const
  · exact continuous_id.inner continuous_const
  · refine UniformSpace.Completion.induction_on y (isClosed_eq ?_ ?_) (fun b => ?_)
    · exact continuous_const.inner continuous_id
    · exact continuous_const.inner (completedTensorMap _ _).continuous
    · rw [g72gk34_ctm_coe, g72gk34_ctm_coe, UniformSpace.Completion.inner_coe,
        UniformSpace.Completion.inner_coe, h0]

lemma g72gk34_ctm_adj (A : H →L[ℂ] H) (B : E →L[ℂ] E) :
    ContinuousLinearMap.adjoint (completedTensorMap A B) =
      completedTensorMap (ContinuousLinearMap.adjoint A) (ContinuousLinearMap.adjoint B) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [g72gk34_inner_ctm, ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint_adjoint]

def g72gk34_pi : (H →L[ℂ] H) →⋆ₐ[ℂ] (NoiseSpace H E →L[ℂ] NoiseSpace H E) where
  toFun A := completedTensorMap A (ContinuousLinearMap.id ℂ E)
  map_one' := g72gk34_ctm_id
  map_mul' A B := by
    change completedTensorMap (A.comp B) (ContinuousLinearMap.id ℂ E) =
      (completedTensorMap A _).comp (completedTensorMap B _)
    rw [g72gk34_ctm_comp]; rfl
  map_zero' := g72gk34_ctm_zero_left _
  map_add' A B := g72gk34_ctm_add_left A B _
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [g72gk34_ctm_smul_left]
    congr 1
    exact g72gk34_ctm_id
  map_star' A := by
    change completedTensorMap (ContinuousLinearMap.adjoint A) (ContinuousLinearMap.id ℂ E) =
      ContinuousLinearMap.adjoint (completedTensorMap A (ContinuousLinearMap.id ℂ E))
    rw [g72gk34_ctm_adj, ContinuousLinearMap.adjoint_id]

lemma g72gk34_pi_apply (A : H →L[ℂ] H) :
    (g72gk34_pi (E := E) A) = completedTensorMap A (ContinuousLinearMap.id ℂ E) := rfl

def g72gk34_J (h0 : H) : E →L[ℂ] NoiseSpace H E :=
  (UniformSpace.Completion.toComplL : H ⊗[ℂ] E →L[ℂ] NoiseSpace H E).comp
    (TensorProduct.mkL ℂ H E h0)

lemma g72gk34_J_apply (h0 : H) (e : E) :
    g72gk34_J h0 e = ((h0 ⊗ₜ[ℂ] e : H ⊗[ℂ] E) : NoiseSpace H E) := rfl

lemma g72gk34_inner_tt (h h' : H) (e e' : E) :
    inner ℂ ((h ⊗ₜ[ℂ] e : H ⊗[ℂ] E) : NoiseSpace H E) ((h' ⊗ₜ[ℂ] e' : H ⊗[ℂ] E) : NoiseSpace H E) =
      inner ℂ h h' * inner ℂ e e' := by
  rw [UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul]

lemma g72gk34_JXJ (h0 : H) (hh0 : ‖h0‖ = 1) (X : E →L[ℂ] E) :
    (ContinuousLinearMap.adjoint (g72gk34_J h0)).comp
      ((completedTensorMap (ContinuousLinearMap.id ℂ H) X).comp (g72gk34_J h0)) = X := by
  have hn : inner ℂ h0 h0 = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hh0]; simp
  ext e
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, g72gk34_J_apply, g72gk34_J_apply, g72gk34_ctm_coe,
    TensorProduct.mapL_tmul, ContinuousLinearMap.id_apply, g72gk34_inner_tt, hn, one_mul]

lemma g72gk34_eext (P Q : NoiseSpace H E →L[ℂ] NoiseSpace H E)
    (h : ∀ (h h' : H) (e e' : E),
      inner ℂ ((h ⊗ₜ[ℂ] e : H ⊗[ℂ] E) : NoiseSpace H E) (P ((h' ⊗ₜ[ℂ] e' : H ⊗[ℂ] E) : NoiseSpace H E)) =
      inner ℂ ((h ⊗ₜ[ℂ] e : H ⊗[ℂ] E) : NoiseSpace H E) (Q ((h' ⊗ₜ[ℂ] e' : H ⊗[ℂ] E) : NoiseSpace H E))) :
    P = Q := by
  have h1 : ∀ a b : H ⊗[ℂ] E, inner ℂ (a : NoiseSpace H E) (P (b : NoiseSpace H E)) =
      inner ℂ (a : NoiseSpace H E) (Q (b : NoiseSpace H E)) := by
    intro a b
    induction a using TensorProduct.induction_on with
    | zero => rw [UniformSpace.Completion.coe_zero, inner_zero_left, inner_zero_left]
    | tmul hh ee =>
      induction b using TensorProduct.induction_on with
      | zero => simp only [UniformSpace.Completion.coe_zero, map_zero, inner_zero_right]
      | tmul hh' ee' => exact h hh hh' ee ee'
      | add b b' hb hb' =>
        rw [UniformSpace.Completion.coe_add, map_add, map_add, inner_add_right, inner_add_right,
          hb, hb']
    | add a a' ha ha' =>
      rw [UniformSpace.Completion.coe_add, inner_add_left, inner_add_left, ha, ha']
  apply g72gk34_text
  intro b
  rw [← sub_eq_zero]
  set z := P (b : NoiseSpace H E) - Q (b : NoiseSpace H E)
  have hz : ∀ w, inner ℂ w z = 0 := by
    intro w
    refine UniformSpace.Completion.induction_on w (isClosed_eq (continuous_id.inner
      continuous_const) continuous_const) (fun a => ?_)
    rw [inner_sub_right, h1 a b, sub_self]
  exact inner_self_eq_zero.mp (hz z)

def g72gk34_R1 (h0 h : H) : H →L[ℂ] H := (innerSL ℂ h0).smulRight h

lemma g72gk34_R1_apply (h0 h v : H) : g72gk34_R1 h0 h v = inner ℂ h0 v • h := by
  simp [g72gk34_R1]

lemma g72gk34_R1_adj_mul (h0 h h' : H) :
    (ContinuousLinearMap.adjoint (g72gk34_R1 h0 h)).comp (g72gk34_R1 h0 h') =
      inner ℂ h h' • g72gk34_R1 h0 h0 := by
  ext v
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.smul_apply, g72gk34_R1_apply, g72gk34_R1_apply, g72gk34_R1_apply]
  simp only [inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

lemma g72gk34_R1_sa (h0 : H) :
    ContinuousLinearMap.adjoint (g72gk34_R1 h0 h0) = g72gk34_R1 h0 h0 := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [g72gk34_R1_apply, g72gk34_R1_apply]
  simp only [inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

lemma g72gk34_commutant (h0 : H) (hh0 : ‖h0‖ = 1) (G : NoiseSpace H E →L[ℂ] NoiseSpace H E)
    (hc : ∀ C : H →L[ℂ] H, (g72gk34_pi (E := E) C).comp G = G.comp (g72gk34_pi C)) :
    G = completedTensorMap (ContinuousLinearMap.id ℂ H)
      ((ContinuousLinearMap.adjoint (g72gk34_J h0)).comp (G.comp (g72gk34_J h0))) := by
  have hn : inner ℂ h0 h0 = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hh0]; simp
  have hR : ∀ (h : H) (e : E), g72gk34_pi (E := E) (g72gk34_R1 h0 h) (g72gk34_J h0 e) =
      ((h ⊗ₜ[ℂ] e : H ⊗[ℂ] E) : NoiseSpace H E) := by
    intro h e
    rw [g72gk34_pi_apply, g72gk34_J_apply, g72gk34_ctm_coe, TensorProduct.mapL_tmul,
      g72gk34_R1_apply, hn, one_smul, ContinuousLinearMap.id_apply]
  apply g72gk34_eext
  intro h h' e e'
  rw [g72gk34_ctm_coe, TensorProduct.mapL_tmul, ContinuousLinearMap.id_apply, g72gk34_inner_tt,
    ← hR h e, ← hR h' e']
  have hc' := congrArg (fun X => X (g72gk34_J h0 e')) (hc (g72gk34_R1 h0 h'))
  simp only [ContinuousLinearMap.comp_apply] at hc'
  rw [← hc', ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    ← map_star, ← ContinuousLinearMap.comp_apply (g72gk34_pi (E := E) (star (g72gk34_R1 h0 h))),
    ← ContinuousLinearMap.mul_def, ← map_mul, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.mul_def, g72gk34_R1_adj_mul, map_smul, ContinuousLinearMap.smul_apply,
    inner_smul_right, ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
    ← map_star, ContinuousLinearMap.star_eq_adjoint, g72gk34_R1_sa]
  rw [show g72gk34_pi (E := E) (g72gk34_R1 h0 h0) (g72gk34_J h0 e) = g72gk34_J h0 e by
    rw [hR h0 e]; rfl]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

end g72gk34t

section g72gk34b_z
variable {A : Type*} [CStarAlgebra A] {H : SeparableHilbertSpace} {K : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma g72gk34b_s0 (f g : (A × H) →₀ ℂ) :
    g72gk34_s (0 : A →ₗ[ℂ] HilbertEndomorphism H) f g = 0 := by
  unfold g72gk34_s
  simp only [LinearMap.zero_apply, ContinuousLinearMap.zero_apply, inner_zero_right, mul_zero]
  simp [Finsupp.sum]

lemma g72gk34b_zero (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K)
    (hd : DenseRange (g72gk34_Phi pi V)) (Y : HilbertEndomorphism K)
    (hY : ∀ a, (pi a).comp Y = Y.comp (pi a)) (hR : ∀ a, compress V ((pi a).comp Y) = 0) :
    Y = 0 := by
  apply g72gk34_ext pi V hd
  intro f g
  rw [g72gk34_Q pi V 0 Y hY (fun a => by rw [hR a, LinearMap.zero_apply]),
    ContinuousLinearMap.zero_apply, inner_zero_right, g72gk34b_s0]

end g72gk34b_z

lemma g72gk34b_csub {H K E : SeparableHilbertSpace} (V : K →L[ℂ] NoiseSpace H E)
    (X Y : NoiseSpace H E →L[ℂ] NoiseSpace H E) :
    compress V X - compress V Y = compress V (X - Y) := by
  simp only [compress, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]

lemma g72gk34b_hmin {H K E : SeparableHilbertSpace}
    (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (V : K →L[ℂ] NoiseSpace H E)
    (hV : IsCanonical T V) :
    (Submodule.span ℂ {z : NoiseSpace H E | ∃ a : HilbertEndomorphism H,
          ∃ eta : K, z = g72gk34_pi (E := E) a (V eta)}).topologicalClosure = ⊤ := by
  have e : {z : NoiseSpace H E | ∃ a : HilbertEndomorphism H, ∃ eta : K,
      z = g72gk34_pi (E := E) a (V eta)} = {z : NoiseSpace H E | ∃ A : HilbertEndomorphism H,
      ∃ eta : K, z = completedTensorMap A (ContinuousLinearMap.id ℂ E) (V eta)} := by
    simp only [g72gk34_pi_apply]
  rw [e]; exact hV.2

lemma g72gk34b_uniq {H K E : SeparableHilbertSpace} [Nontrivial H]
    (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (V : K →L[ℂ] NoiseSpace H E)
    (hV : IsCanonical T V) (F Y : HilbertEndomorphism E)
    (hYF : ∀ A, compress V (completedTensorMap A Y) = compress V (completedTensorMap A F)) :
    Y = F := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  obtain ⟨h0, hh0⟩ : ∃ h0 : H, ‖h0‖ = 1 := ⟨_, norm_smul_inv_norm (𝕜 := ℂ) hv⟩
  obtain ⟨D, hD⟩ : ∃ D, D = Y - F := ⟨_, rfl⟩
  have hRz : ∀ A, compress V ((g72gk34_pi (E := E) A).comp
        (completedTensorMap (ContinuousLinearMap.id ℂ H) D)) = 0 := by
    intro A
    rw [g72gk34_pi_apply, g72gk34_ctm_comp, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.id_comp, hD, g72gk34_ctm_sub_right, ← g72gk34b_csub, hYF A, sub_self]
  have hcommD : ∀ A, (g72gk34_pi (E := E) A).comp
      (completedTensorMap (ContinuousLinearMap.id ℂ H) D) =
      (completedTensorMap (ContinuousLinearMap.id ℂ H) D).comp (g72gk34_pi A) := by
    intro A
    rw [g72gk34_pi_apply, g72gk34_ctm_comp, g72gk34_ctm_comp, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
  have hd := g72gk34_dense (A := HilbertEndomorphism H) (g72gk34_pi (E := E)) V (g72gk34b_hmin T V hV)
  have h0D : completedTensorMap (ContinuousLinearMap.id ℂ H) D = 0 :=
    g72gk34b_zero (A := HilbertEndomorphism H) (g72gk34_pi (E := E)) V hd _ hcommD hRz
  have := g72gk34_JXJ (E := E) h0 hh0 D
  rw [h0D, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero] at this
  rw [← sub_eq_zero, ← hD]
  exact this.symm

lemma g72gk34b_fwd {H K E : SeparableHilbertSpace} [Nontrivial H]
    (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (V : K →L[ℂ] NoiseSpace H E)
    (hV : IsCanonical T V)
    (S : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (hS : GramCompletelyPositive S)
    (hdom : CompletelyDominated S T) :
    ∃ F : HilbertEndomorphism E, PositiveContraction F ∧
      ∀ A, S A = compress V (completedTensorMap A F) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  obtain ⟨h0, hh0⟩ : ∃ h0 : H, ‖h0‖ = 1 := ⟨_, norm_smul_inv_norm (𝕜 := ℂ) hv⟩
  let Ti : Bool → HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K :=
    fun b => if b then S else T - S
  have hgram : ∀ b, GramCompletelyPositive (Ti b) := by
    intro b; cases b
    · exact hdom
    · exact hS
  have hsum : T = ∑ b, Ti b := by
    rw [Fintype.sum_bool]; simp [Ti]
  have hdil : ∀ A, T A = compress V (g72gk34_pi (E := E) A) := by
    intro A; rw [g72gk34_pi_apply]; exact hV.1 A
  obtain ⟨Fs, ⟨hpos, hsumF, hcomp⟩, _⟩ := g72gk34_rn T (g72gk34_pi (E := E)) V
    hdil (g72gk34b_hmin T V hV) Bool Ti hgram hsum
  obtain ⟨J, hJ⟩ : ∃ J, J = g72gk34_J (E := E) h0 := ⟨_, rfl⟩
  have hGF : Fs true = completedTensorMap (ContinuousLinearMap.id ℂ H)
      ((ContinuousLinearMap.adjoint J).comp ((Fs true).comp J)) := by
    rw [hJ]; exact g72gk34_commutant h0 hh0 (Fs true) (hpos true).2
  have hidG : ContinuousLinearMap.id ℂ _ - Fs true = Fs false := by
    rw [← hsumF, Fintype.sum_bool]; simp
  have hJJ : (ContinuousLinearMap.adjoint J).comp ((ContinuousLinearMap.id ℂ _).comp J) =
      ContinuousLinearMap.id ℂ E := by
    have := g72gk34_JXJ (E := E) h0 hh0 (ContinuousLinearMap.id ℂ E)
    rw [g72gk34_ctm_id] at this
    rw [hJ]; exact this
  refine ⟨(ContinuousLinearMap.adjoint J).comp ((Fs true).comp J),
    ⟨(hpos true).1.adjoint_conj J, ?_⟩, ?_⟩
  · have : ContinuousLinearMap.id ℂ E - (ContinuousLinearMap.adjoint J).comp ((Fs true).comp J) =
        (ContinuousLinearMap.adjoint J).comp ((Fs false).comp J) := by
      rw [← hidG, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, hJJ]
    rw [this]
    exact (hpos false).1.adjoint_conj J
  · intro A
    have h1 : S A = compress V ((g72gk34_pi (E := E) A).comp (Fs true)) := hcomp true A
    rw [h1]
    conv_lhs => rw [hGF, g72gk34_pi_apply, g72gk34_ctm_comp, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.id_comp]

lemma g72gk34b_bwd {H K E : SeparableHilbertSpace}
    (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (V : K →L[ℂ] NoiseSpace H E)
    (hV : IsCanonical T V)
    (S : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (F : HilbertEndomorphism E)
    (hF : PositiveContraction F) (hSF : ∀ A, S A = compress V (completedTensorMap A F)) :
    CompletelyDominated S T := by
  obtain ⟨D, hDdef⟩ : ∃ D, D = ContinuousLinearMap.id ℂ E - F := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hDdef]; exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hF.2
  obtain ⟨R, hRdef⟩ : ∃ R, R = CFC.sqrt D := ⟨_, rfl⟩
  have hRR : R * R = D := by rw [hRdef]; exact CFC.sqrt_mul_sqrt_self D hD0
  have hRs : ContinuousLinearMap.adjoint R = R := by
    rw [← ContinuousLinearMap.star_eq_adjoint, hRdef]
    exact (CFC.sqrt_nonneg D).isSelfAdjoint.star_eq
  have hTS : ∀ A, (T - S) A = compress V (completedTensorMap A D) := by
    intro A
    rw [LinearMap.sub_apply, hV.1 A, hSF A, g72gk34b_csub, ← g72gk34_ctm_sub_right, hDdef]
  intro n a eta
  have key : ∀ i j, inner ℂ (eta i) ((T - S) (star (a i) * a j) (eta j)) =
      inner ℂ (completedTensorMap (a i) R (V (eta i)))
        (completedTensorMap (a j) R (V (eta j))) := by
    intro i j
    rw [hTS, ← hRR, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.mul_def, ← g72gk34_ctm_comp, ← hRs, ← g72gk34_ctm_adj, hRs,
      compress, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right]
  simp only [key]
  have hsum : (∑ i, ∑ j, inner ℂ (completedTensorMap (a i) R (V (eta i)))
        (completedTensorMap (a j) R (V (eta j)))) =
      inner ℂ (∑ i, completedTensorMap (a i) R (V (eta i)))
        (∑ j, completedTensorMap (a j) R (V (eta j))) := by
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ => (inner_sum _ _ _).symm
  rw [hsum, inner_self_eq_norm_sq_to_K]
  constructor <;> simp [sq, mul_self_nonneg]

theorem g72gk34b_canon (H K E : SeparableHilbertSpace)
    (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (V : K →L[ℂ] NoiseSpace H E)
    (hT : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T) (hV : IsCanonical T V)
    (S : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (hS : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) S) :
    CompletelyDominated S T ↔ ∃ F : HilbertEndomorphism E, PositiveContraction F ∧
      (∀ A, S A = compress V (completedTensorMap A F)) ∧
      (Nontrivial H → ∀ Y : HilbertEndomorphism E,
        (∀ A, S A = compress V (completedTensorMap A Y)) → Y = F) := by
  constructor
  · intro hdom
    by_cases hH : Nontrivial H
    · obtain ⟨F, hF, hSF⟩ := g72gk34b_fwd T V hV S hS.1 hdom
      refine ⟨F, hF, hSF, fun _ Y hY => g72gk34b_uniq T V hV F Y fun A => ?_⟩
      rw [← hY A, hSF A]
    · have hsub : Subsingleton H := not_nontrivial_iff_subsingleton.mp hH
      have hA : ∀ A : HilbertEndomorphism H, A = 0 := fun A => by
        ext x; exact Subsingleton.elim _ _
      refine ⟨0, ⟨ContinuousLinearMap.isPositive_zero, by
        simpa using ContinuousLinearMap.isPositive_id⟩, fun A => ?_, fun h => absurd h hH⟩
      rw [hA A, map_zero, g72gk34_ctm_zero_left]
      simp [compress]
  · rintro ⟨F, hF, hSF, _⟩
    exact g72gk34b_bwd T V hV S F hF hSF


section g72gk34b_fk
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {X : Type} [Fintype X]

def g72gk34b_mat (e : X → E) (G : E →L[ℂ] E) : Matrix X X ℂ :=
  Matrix.of fun a b => inner ℂ (e a) (G (e b))

lemma g72gk34b_mat_apply (e : X → E) (G : E →L[ℂ] E) (a b : X) :
    g72gk34b_mat e G a b = inner ℂ (e a) (G (e b)) := rfl

lemma g72gk34b_quad (e : X → E) (G : E →L[ℂ] E) (v : X → ℂ) :
    star v ⬝ᵥ (g72gk34b_mat e G *ᵥ v) =
      inner ℂ (∑ a, v a • e a) (G (∑ b, v b • e b)) := by
  simp only [dotProduct, Matrix.mulVec, g72gk34b_mat_apply, map_sum, map_smul, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum, Pi.star_apply, RCLike.star_def]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma g72gk34b_expand (e : HilbertBasis X ℂ E) (z : E) :
    z = ∑ a, (inner ℂ (e a) z) • e a := by
  have h := e.hasSum_repr z
  calc z = ∑ i, e.repr z i • e i := ((hasSum_fintype _).unique h).symm
    _ = _ := by simp only [HilbertBasis.repr_apply_apply]

lemma g72gk34b_psd_of_pos (e : X → E) (G : E →L[ℂ] E) (hG : G.IsPositive) :
    Matrix.PosSemidef (g72gk34b_mat e G) := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · refine Matrix.IsHermitian.ext fun a b => ?_
    rw [g72gk34b_mat_apply, g72gk34b_mat_apply, RCLike.star_def, inner_conj_symm]
    exact hG.isSymmetric _ _
  · rw [g72gk34b_quad]
    set z := ∑ a, v a • e a
    have h := (ContinuousLinearMap.isPositive_iff_complex G).1 hG z
    rw [← inner_conj_symm, ← h.1, Complex.conj_ofReal]
    exact Complex.zero_le_real.mpr h.2

lemma g72gk34b_pos_of_psd (e : HilbertBasis X ℂ E) (G : E →L[ℂ] E)
    (hG : Matrix.PosSemidef (g72gk34b_mat e G)) :
    G.IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro z
  have hq := hG.dotProduct_mulVec_nonneg (fun a => inner ℂ (e a) z)
  rw [g72gk34b_quad, ← g72gk34b_expand e z] at hq
  have h2 : inner ℂ (G z) z = inner ℂ z (G z) := by
    rw [← inner_conj_symm]
    obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ inner ℂ z (G z) = (r : ℂ) := by
      refine ⟨(inner ℂ z (G z)).re, Complex.nonneg_iff.1 hq |>.1, ?_⟩
      apply Complex.ext <;> simp [(Complex.nonneg_iff.1 hq).2.symm]
    rw [hr, Complex.conj_ofReal]
  rw [h2]
  obtain ⟨h0, him⟩ := Complex.nonneg_iff.1 hq
  refine ⟨?_, h0⟩
  apply Complex.ext <;> simp [him.symm]

def g72gk34b_op (e : X → E) (Mx : Matrix X X ℂ) : E →L[ℂ] E :=
  ∑ x, ∑ y, Mx x y • (innerSL ℂ (e y)).smulRight (e x)

lemma g72gk34b_op_entry (e : HilbertBasis X ℂ E) (Mx : Matrix X X ℂ) (a b : X) :
    inner ℂ (e a) (g72gk34b_op e Mx (e b)) = Mx a b := by
  classical
  have ho := orthonormal_iff_ite.1 e.orthonormal
  simp only [g72gk34b_op, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_sum, inner_smul_right, ho]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma g72gk34b_one_sub (e : HilbertBasis X ℂ E) (G : E →L[ℂ] E) :
    g72gk34b_mat e (ContinuousLinearMap.id ℂ E - G) = 1 - g72gk34b_mat e G := by
  classical
  ext a b
  have ho := orthonormal_iff_ite.1 e.orthonormal a b
  rw [Matrix.sub_apply, g72gk34b_mat_apply, g72gk34b_mat_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, inner_sub_right, ho, Matrix.one_apply]

end g72gk34b_fk

lemma g72gk34b_ctv {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (h : H) (x : E) :
    completedTensorVector h x = (((h ⊗ₜ[ℂ] x : H ⊗[ℂ] E)) : NoiseSpace H E) := rfl

lemma g72gk34b_kform {H K E : SeparableHilbertSpace} {X : Type} [Fintype X]
    (e : HilbertBasis X ℂ E) (V : K →L[ℂ] NoiseSpace H E) (W : X → K →L[ℂ] H)
    (hW : IsInducedKraus e V W) (A : HilbertEndomorphism H) (F : HilbertEndomorphism E) :
    compress V (completedTensorMap A F) = ∑ x, ∑ y, inner ℂ (e x) (F (e y)) •
      (ContinuousLinearMap.adjoint (W x)).comp (A.comp (W y)) := by
  have hV : ∀ η, V η = ∑ x, completedTensorVector (W x η) (e x) := fun η =>
    (hW η).unique (hasSum_fintype _)
  ext η
  apply ext_inner_left ℂ
  intro ξ
  rw [compress, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, hV ξ, hV η]
  simp only [map_sum, sum_inner, inner_sum, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, g72gk34b_ctv, g72gk34_ctm_coe,
    TensorProduct.mapL_tmul, g72gk34_inner_tt]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem solution (H K E : SeparableHilbertSpace)
    (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (V : K →L[ℂ] NoiseSpace H E)
    (hT : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T) (hV : IsCanonical T V)
    (X : Type) [Fintype X] (e : HilbertBasis X ℂ E)
    (W : X → K →L[ℂ] H) (hW : IsInducedKraus e V W)
    (S : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) (hS : IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) S) :
    CompletelyDominated S T ↔ ∃ M : Matrix X X ℂ, M.PosSemidef ∧ (1 - M).PosSemidef ∧
      ∀ A : HilbertEndomorphism H, S A = ∑ x, ∑ y,
        M x y • (ContinuousLinearMap.adjoint (W x)).comp (A.comp (W y)) := by
  constructor
  · intro hdom
    obtain ⟨F, hF, hSF, -⟩ := (g72gk34b_canon H K E T V hT hV S hS).1 hdom
    refine ⟨g72gk34b_mat e F, g72gk34b_psd_of_pos _ F hF.1, ?_, fun A => ?_⟩
    · rw [← g72gk34b_one_sub]; exact g72gk34b_psd_of_pos _ _ hF.2
    · rw [hSF A, g72gk34b_kform e V W hW]; rfl
  · rintro ⟨Mx, h1, h2, hSA⟩
    have hent : g72gk34b_mat e (g72gk34b_op e Mx) = Mx := by
      ext a b; exact g72gk34b_op_entry e Mx a b
    refine g72gk34b_bwd T V hV S (g72gk34b_op e Mx)
      ⟨g72gk34b_pos_of_psd e _ (by rw [hent]; exact h1), g72gk34b_pos_of_psd e _ ?_⟩ fun A => ?_
    · rw [g72gk34b_one_sub, hent]; exact h2
    · rw [hSA A, g72gk34b_kform e V W hW]
      simp only [g72gk34b_op_entry]

end
