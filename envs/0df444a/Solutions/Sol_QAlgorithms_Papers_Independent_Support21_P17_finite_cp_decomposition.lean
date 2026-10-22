-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P17.finite_cp_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T18:00:05.459043+00:00
-- url     : https://prove2.me/submissions/a4548072-aebf-4611-a6a7-2b897363706d

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
variable {A : Type*} [CStarAlgebra A] {H K : SeparableHilbertSpace}

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
    (hmin : IsMinimal pi V) : DenseRange (g72gk34_Phi pi V) := by
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
    (hY : CommutesWithRepresentation pi Y) (hR : ∀ a, R a = compress V ((pi a).comp Y))
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

theorem solution {A : Type*} [CStarAlgebra A]
    (G H K : SeparableHilbertSpace) (rho : A →⋆ₐ[ℂ] HilbertEndomorphism G) (h_rho : Function.Injective rho)
    (T : A →ₗ[ℂ] HilbertEndomorphism H) (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K)
    (hT : IsNormalCP rho T) (h_dilation : ∀ a, T a = compress V (pi a))
    (h_minimal : IsMinimal pi V) (I : Type*) [Fintype I]
    (Ti : I → A →ₗ[ℂ] HilbertEndomorphism H) (hTi : ∀ i, IsNormalCP rho (Ti i))
    (h_sum : T = ∑ i, Ti i) :
    ∃! F : I → HilbertEndomorphism K,
      (∀ i, (F i).IsPositive ∧ CommutesWithRepresentation pi (F i)) ∧
      (∑ i, F i) = ContinuousLinearMap.id ℂ K ∧
      ∀ i a, Ti i a = compress V ((pi a).comp (F i)) := by
  have hd := g72gk34_dense pi V h_minimal
  have hgram : ∀ i, GramCompletelyPositive (Ti i) := fun i => (hTi i).1
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
  have hcomm : ∀ i, CommutesWithRepresentation pi (F i) := by
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
