-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P17.stinespring_radon_nikodym
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:53:10.993074+00:00
-- url     : https://prove2.me/submissions/67065a44-3763-4c71-8b1d-4d26dee80097

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct InnerProductSpace

open Filter

namespace RNAux

section Herm
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

lemma herm_of_real (B : M →ₛₗ[starRingEnd ℂ] M →ₗ[ℂ] ℂ) (h : ∀ f, (B f f).im = 0) (f g : M) :
    B f g = conj (B g f) := by
  have h1 := h (f + g)
  have h2 := h (f + Complex.I • g)
  have e1 : B (f + g) (f + g) = B f f + B f g + B g f + B g g := by
    simp only [map_add, LinearMap.add_apply]; ring
  have e2 : B (f + Complex.I • g) (f + Complex.I • g) =
      B f f + Complex.I * B f g + (-Complex.I) * B g f + B g g := by
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      Complex.conj_I]
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (-(B g g)) * this
  rw [e1] at h1
  rw [e2] at h2
  have hf := h f
  have hg := h g
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_im,
    Complex.neg_re, hf, hg] at h1 h2
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith


lemma cs_bound (B : M →ₛₗ[starRingEnd ℂ] M →ₗ[ℂ] ℂ) (hr : ∀ f, (B f f).im = 0)
    (hp : ∀ f, 0 ≤ (B f f).re) (f g : M) :
    ‖B f g‖ ^ 2 ≤ (B f f).re * (B g g).re := by
  let c : PreInnerProductSpace.Core ℂ M :=
    { inner := fun x y => B x y
      conj_inner_symm := fun x y => (herm_of_real B hr x y).symm
      re_inner_nonneg := hp
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp }
  have this : ‖B f g‖ * ‖B g f‖ ≤ (B f f).re * (B g g).re :=
    InnerProductSpace.Core.inner_mul_inner_self_le (c := c) f g
  have h2 : ‖B g f‖ = ‖B f g‖ := by
    rw [herm_of_real B hr g f]; simp
  rw [h2] at this
  simpa [sq] using this

end Herm

section Main
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem exists_op (θ : M →ₗ[ℂ] K) (hd : DenseRange θ) (B : M →ₛₗ[starRingEnd ℂ] M →ₗ[ℂ] ℂ)
    (hr : ∀ f, (B f f).im = 0) (hp : ∀ f, 0 ≤ (B f f).re) (hle : ∀ f, (B f f).re ≤ ‖θ f‖ ^ 2) :
    ∃ F : K →L[ℂ] K, (∀ f g, B f g = ⟪θ f, F (θ g)⟫_ℂ) ∧ F.IsPositive ∧
      (ContinuousLinearMap.id ℂ K - F).IsPositive := by
  have hbd : ∀ f g, ‖B f g‖ ≤ ‖θ g‖ * ‖θ f‖ := by
    intro f g
    have h1 := cs_bound B hr hp f g
    have h2 : (B f f).re * (B g g).re ≤ ‖θ f‖ ^ 2 * ‖θ g‖ ^ 2 :=
      mul_le_mul (hle f) (hle g) (hp g) (sq_nonneg _)
    have h3 : ‖B f g‖ ^ 2 ≤ (‖θ g‖ * ‖θ f‖) ^ 2 := by
      calc ‖B f g‖ ^ 2 ≤ _ := h1.trans h2
        _ = _ := by ring
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h3
  let lam : M → (M →ₗ[ℂ] ℂ) := fun g =>
    { toFun := fun f => starRingEnd ℂ (B f g)
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  have hlam : ∀ g f, ‖lam g f‖ ≤ ‖θ g‖ * ‖θ f‖ := by
    intro g f
    simpa [lam] using hbd f g
  let Lam : M → (K →L[ℂ] ℂ) := fun g => (lam g).extendOfNorm θ
  have hLam : ∀ g f, Lam g (θ f) = starRingEnd ℂ (B f g) := by
    intro g f
    exact LinearMap.extendOfNorm_eq hd ⟨‖θ g‖, hlam g⟩ f
  have hLamn : ∀ g, ‖Lam g‖ ≤ ‖θ g‖ := fun g =>
    LinearMap.opNorm_extendOfNorm_le hd (norm_nonneg _) (hlam g)
  have hLam_add : ∀ g1 g2, Lam (g1 + g2) = Lam g1 + Lam g2 := by
    intro g1 g2
    ext1 x
    refine hd.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro f
    simp [hLam]
  have hLam_smul : ∀ (c : ℂ) g, Lam (c • g) = starRingEnd ℂ c • Lam g := by
    intro c g
    ext1 x
    refine hd.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro f
    simp [hLam]
  let G : M →ₗ[ℂ] K :=
    { toFun := fun g => (InnerProductSpace.toDual ℂ K).symm (Lam g)
      map_add' := by intros; simp [hLam_add]
      map_smul' := by intros; simp only [hLam_smul, map_smulₛₗ, Complex.conj_conj, RingHom.id_apply] }
  have hG : ∀ g f, ⟪θ f, G g⟫_ℂ = B f g := by
    intro g f
    have : ⟪G g, θ f⟫_ℂ = Lam g (θ f) := InnerProductSpace.toDual_symm_apply
    rw [← inner_conj_symm, this, hLam]; simp
  have hGn : ∀ g, ‖G g‖ ≤ 1 * ‖θ g‖ := by
    intro g
    have : ‖G g‖ = ‖Lam g‖ := by simp [G]
    rw [this, one_mul]; exact hLamn g
  let F : K →L[ℂ] K := G.extendOfNorm θ
  have hF : ∀ g, F (θ g) = G g := fun g => LinearMap.extendOfNorm_eq hd ⟨1, hGn⟩ g
  have hBF : ∀ f g, B f g = ⟪θ f, F (θ g)⟫_ℂ := by
    intro f g; rw [hF, hG]
  have hq : ∀ f, ⟪F (θ f), θ f⟫_ℂ = ((B f f).re : ℂ) := by
    intro f
    rw [← inner_conj_symm, ← hBF]
    apply Complex.ext <;> simp [hr f]
  refine ⟨F, hBF, ?_, ?_⟩
  · rw [ContinuousLinearMap.isPositive_iff_complex]
    intro x
    refine hd.induction_on x ?_ ?_
    · rw [Set.ofPred_and]
      exact (isClosed_eq (by fun_prop) (by fun_prop)).inter (isClosed_le (by fun_prop) (by fun_prop))
    · intro f
      rw [hq]
      simp [hp f]
  · rw [ContinuousLinearMap.isPositive_iff_complex]
    intro x
    refine hd.induction_on x ?_ ?_
    · rw [Set.ofPred_and]
      exact (isClosed_eq (by fun_prop) (by fun_prop)).inter (isClosed_le (by fun_prop) (by fun_prop))
    · intro f
      have : ⟪θ f, θ f⟫_ℂ = ((‖θ f‖ ^ 2 : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K]; simp
      have key : ⟪(ContinuousLinearMap.id ℂ K - F) (θ f), θ f⟫_ℂ
          = ((‖θ f‖ ^ 2 - (B f f).re : ℝ) : ℂ) := by
        simp only [sub_apply, ContinuousLinearMap.id_apply, inner_sub_left, hq, this]
        push_cast; ring
      have h2 : 0 ≤ ‖θ f‖ ^ 2 - (B f f).re := by linarith [hle f]
      generalize ‖θ f‖ ^ 2 - (B f f).re = r at key h2
      rw [key]
      exact ⟨by simp, by simpa using h2⟩
end Main



section Concrete
variable {A : Type*} [CStarAlgebra A] {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

abbrev Sg (A H : Type*) := (A × H) →₀ ℂ

def b0 (R : A →ₗ[ℂ] (H →L[ℂ] H)) (p q : A × H) : ℂ := ⟪p.2, R (star p.1 * q.1) q.2⟫_ℂ

def conjF : Sg A H →ₛₗ[starRingEnd ℂ] Sg A H where
  toFun f := Finsupp.mapRange (starRingEnd ℂ) (map_zero _) f
  map_add' f g := Finsupp.mapRange_add (map_add _) f g
  map_smul' c f := by ext p; simp

def Cf (R : A →ₗ[ℂ] (H →L[ℂ] H)) : Sg A H →ₗ[ℂ] Sg A H →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun p => Finsupp.linearCombination ℂ (b0 R p))

def Bf (R : A →ₗ[ℂ] (H →L[ℂ] H)) : Sg A H →ₛₗ[starRingEnd ℂ] Sg A H →ₗ[ℂ] ℂ :=
  (Cf R).comp conjF

lemma Bf_single (R : A →ₗ[ℂ] (H →L[ℂ] H)) (p q : A × H) (c d : ℂ) :
    Bf R (Finsupp.single p c) (Finsupp.single q d) = starRingEnd ℂ c * d * b0 R p q := by
  simp [Bf, Cf, conjF, Finsupp.linearCombination_single]
  ring

lemma Bf_apply (R : A →ₗ[ℂ] (H →L[ℂ] H)) (f g : Sg A H) :
    Bf R f g = ∑ p ∈ f.support, ∑ q ∈ g.support, starRingEnd ℂ (f p) * g q * b0 R p q := by
  have : Bf R f g = (Finsupp.mapRange (starRingEnd ℂ) (map_zero _) f).sum
      (fun p c => c * (g.sum fun q d => d * b0 R p q)) := by
    simp [Bf, Cf, conjF, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]
  rw [this, Finsupp.sum_of_support_subset _ (Finsupp.support_mapRange) _ (by simp)]
  simp only [Finsupp.mapRange_apply, Finsupp.sum, Finset.mul_sum, mul_assoc]


def GramRaw (R : A →ₗ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ (n : ℕ) (a : Fin n → A) (eta : Fin n → H),
    (∑ i, ∑ j, ⟪eta i, R (star (a i) * a j) (eta j)⟫_ℂ).im = 0 ∧
    0 ≤ (∑ i, ∑ j, ⟪eta i, R (star (a i) * a j) (eta j)⟫_ℂ).re

lemma gram_pos (R : A →ₗ[ℂ] (H →L[ℂ] H)) (hR : GramRaw R) (f : Sg A H) :
    (Bf R f f).im = 0 ∧ 0 ≤ (Bf R f f).re := by
  classical
  set s := f.support with hs
  let e : s ≃ Fin s.card := s.equivFin
  let p : Fin s.card → A × H := fun i => (e.symm i).1
  have key : (∑ i : Fin s.card, ∑ j : Fin s.card,
      ⟪(fun i => (p i).2) i, R (star (f (p i) • (p i).1) * (f (p j) • (p j).1)) ((fun i => (p i).2) j)⟫_ℂ)
      = Bf R f f := by
    rw [Bf_apply]
    have h1 : ∀ φ : A × H → ℂ, ∑ i : Fin s.card, φ (p i) = ∑ x ∈ s, φ x := by
      intro φ
      have := Equiv.sum_comp e.symm (fun x : s => φ x.1)
      rw [Finset.sum_coe_sort s φ] at this
      exact this
    simp only [star_smul, smul_mul_smul_comm, map_smul, smul_apply,
      inner_smul_right]
    have h2 : ∀ φ : A × H → A × H → ℂ,
        ∑ i : Fin s.card, ∑ j : Fin s.card, φ (p i) (p j) = ∑ x ∈ s, ∑ y ∈ s, φ x y := by
      intro φ
      rw [h1 (fun x => ∑ j : Fin s.card, φ x (p j))]
      exact Finset.sum_congr rfl fun x _ => h1 (φ x)
    exact h2 (fun x y => star (f x) * f y * b0 R x y)
  have := hR s.card (fun i => f (p i) • (p i).1) (fun i => (p i).2)
  rw [key] at this
  exact this


lemma Sg_induct2 {P : Sg A H → Sg A H → Prop}
    (h0 : ∀ g, P 0 g) (h0' : ∀ f, P f 0)
    (ha : ∀ f1 f2 g, P f1 g → P f2 g → P (f1 + f2) g)
    (ha' : ∀ f g1 g2, P f g1 → P f g2 → P f (g1 + g2))
    (hs : ∀ p c q d, P (Finsupp.single p c) (Finsupp.single q d)) : ∀ f g, P f g := by
  intro f g
  induction f using Finsupp.induction_linear with
  | zero => exact h0 g
  | add f1 f2 h1 h2 => exact ha _ _ _ h1 h2
  | single p c =>
    induction g using Finsupp.induction_linear with
    | zero => exact h0' _
    | add g1 g2 h1 h2 => exact ha' _ _ _ h1 h2
    | single q d => exact hs p c q d

lemma Bf_sub (R1 R2 : A →ₗ[ℂ] (H →L[ℂ] H)) (f g : Sg A H) :
    Bf (R1 - R2) f g = Bf R1 f g - Bf R2 f g := by
  refine Sg_induct2 (P := fun f g => Bf (R1 - R2) f g = Bf R1 f g - Bf R2 f g)
    (by simp) (by simp) ?_ ?_ ?_ f g
  · intro f1 f2 g h1 h2
    simp only [map_add, LinearMap.add_apply] at *
    rw [h1, h2]; ring
  · intro f g1 g2 h1 h2
    simp only [map_add, LinearMap.add_apply] at *
    rw [h1, h2]; ring
  · intro p c q d
    simp only [Bf_single, b0, LinearMap.sub_apply, ContinuousLinearMap.sub_apply, inner_sub_right]
    ring

variable (pi : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (V : H →L[ℂ] K)

def theta : Sg A H →ₗ[ℂ] K := Finsupp.linearCombination ℂ (fun p : A × H => pi p.1 (V p.2))

lemma theta_single (p : A × H) (c : ℂ) : theta pi V (Finsupp.single p c) = c • pi p.1 (V p.2) := by
  simp [theta, Finsupp.linearCombination_single]

lemma inner_pi (a b : A) (x y : K) : ⟪pi a x, pi b y⟫_ℂ = ⟪x, pi (star a * b) y⟫_ℂ := by
  have : ContinuousLinearMap.adjoint (pi a) = pi (star a) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, map_star]
  rw [← ContinuousLinearMap.adjoint_inner_right (pi a), this, map_mul]; rfl

lemma Bf_T (T : A →ₗ[ℂ] (H →L[ℂ] H))
    (hT : ∀ a, T a = (ContinuousLinearMap.adjoint V).comp ((pi a).comp V)) (f g : Sg A H) :
    Bf T f g = ⟪theta pi V f, theta pi V g⟫_ℂ := by
  refine Sg_induct2 (P := fun f g => Bf T f g = ⟪theta pi V f, theta pi V g⟫_ℂ)
    (by simp) (by simp) ?_ ?_ ?_ f g
  · intro f1 f2 g h1 h2
    simp only [map_add, LinearMap.add_apply, inner_add_left] at *
    rw [h1, h2]
  · intro f g1 g2 h1 h2
    simp only [map_add, LinearMap.add_apply, inner_add_right] at *
    rw [h1, h2]
  · intro p c q d
    rw [Bf_single, theta_single, theta_single, inner_smul_left, inner_smul_right, inner_pi]
    simp only [b0, hT, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    ring


def act (c : A) : Sg A H →ₗ[ℂ] Sg A H :=
  Finsupp.lmapDomain ℂ ℂ (fun p : A × H => (c * p.1, p.2))

lemma act_single (c : A) (p : A × H) (d : ℂ) :
    act c (Finsupp.single p d) = Finsupp.single (c * p.1, p.2) d := by
  simp [act, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

lemma theta_act (c : A) (g : Sg A H) : theta pi V (act c g) = pi c (theta pi V g) := by
  have : (theta pi V).comp (act c) = (pi c : K →L[ℂ] K).toLinearMap.comp (theta pi V) := by
    refine Finsupp.lhom_ext fun p d => ?_
    simp [act_single, theta_single, map_mul, mul_assoc]
  exact LinearMap.congr_fun this g

lemma Bf_comm (S : A →ₗ[ℂ] (H →L[ℂ] H)) (c : A) (f g : Sg A H) :
    Bf S f (act c g) = Bf S (act (star c) f) g := by
  refine Sg_induct2 (P := fun f g => Bf S f (act c g) = Bf S (act (star c) f) g)
    (by simp) (by simp) ?_ ?_ ?_ f g
  · intro f1 f2 g h1 h2
    simp only [map_add, LinearMap.add_apply] at *
    rw [h1, h2]
  · intro f g1 g2 h1 h2
    simp only [map_add, LinearMap.add_apply] at *
    rw [h1, h2]
  · intro p c0 q d
    rw [act_single, act_single, Bf_single, Bf_single]
    simp only [b0, star_mul, star_star, mul_assoc]

lemma eq_zero_of_inner_range {θ : Sg A H →ₗ[ℂ] K} (hd : DenseRange θ) (w : K)
    (h : ∀ f, ⟪θ f, w⟫_ℂ = 0) : w = 0 := by
  have : ∀ x, ⟪x, w⟫_ℂ = 0 := fun x =>
    hd.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) h
  exact inner_self_eq_zero.mp (this w)

lemma theta_dense (hmin : (Submodule.span ℂ {z : K | ∃ a : A, ∃ eta : H, z = pi a (V eta)}).topologicalClosure = ⊤) :
    DenseRange (theta pi V) := by
  have h1 : LinearMap.range (theta pi V) =
      Submodule.span ℂ {z : K | ∃ a : A, ∃ eta : H, z = pi a (V eta)} := by
    rw [theta, Finsupp.range_linearCombination]
    congr 1
    ext z
    constructor
    · rintro ⟨p, rfl⟩; exact ⟨p.1, p.2, rfl⟩
    · rintro ⟨a, η, rfl⟩; exact ⟨(a, η), rfl⟩
  have h2 : Dense ((LinearMap.range (theta pi V) : Submodule ℂ K) : Set K) := by
    rw [h1]; exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hmin
  rw [DenseRange, ← LinearMap.coe_range]; exact h2


lemma adjoint_pi (a : A) : ContinuousLinearMap.adjoint (pi a) = pi (star a) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, map_star]

theorem exists_RN (T S : A →ₗ[ℂ] (H →L[ℂ] H))
    (hT : ∀ a, T a = (ContinuousLinearMap.adjoint V).comp ((pi a).comp V))
    (hmin : (Submodule.span ℂ {z : K | ∃ a : A, ∃ eta : H, z = pi a (V eta)}).topologicalClosure = ⊤)
    (hS : GramRaw S) (hD : GramRaw (T - S)) :
    ∃ F : K →L[ℂ] K, F.IsPositive ∧ (ContinuousLinearMap.id ℂ K - F).IsPositive ∧
      (∀ a, (pi a).comp F = F.comp (pi a)) ∧
      ∀ a, S a = (ContinuousLinearMap.adjoint V).comp (((pi a).comp F).comp V) := by
  have hd := theta_dense pi V hmin
  obtain ⟨F, hBF, hF1, hF2⟩ := exists_op (theta pi V) hd (Bf S)
    (fun f => (gram_pos S hS f).1) (fun f => (gram_pos S hS f).2) (by
      intro f
      have h1 := (gram_pos _ hD f).2
      rw [Bf_sub, Bf_T pi V T hT] at h1
      have h2 : ((⟪theta pi V f, theta pi V f⟫_ℂ).re) = ‖theta pi V f‖ ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K]; simp [← Complex.ofReal_pow]
      rw [Complex.sub_re, h2] at h1
      linarith)
  have hcomm : ∀ c x, F (pi c x) = pi c (F x) := by
    intro c x
    refine hd.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro g
    rw [← sub_eq_zero]
    refine eq_zero_of_inner_range hd _ fun f => ?_
    rw [inner_sub_right, ← theta_act pi V c g, ← hBF, Bf_comm, hBF, theta_act, ← adjoint_pi pi c,
      ContinuousLinearMap.adjoint_inner_left]
    exact sub_self _
  refine ⟨F, hF1, hF2, ?_, ?_⟩
  · intro a
    ext1 x
    exact (hcomm a x).symm
  · intro a
    ext1 ξ
    refine ext_inner_left ℂ fun η => ?_
    have h := hBF (Finsupp.single (1, η) 1) (Finsupp.single (a, ξ) 1)
    rw [Bf_single, theta_single, theta_single] at h
    simp only [b0, map_one, one_smul, star_one, one_mul, ContinuousLinearMap.one_apply,
      map_one, map_one, RingHom.id_apply, map_one] at h
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    rw [h, hcomm]


theorem commutant_zero
    (hmin : (Submodule.span ℂ {z : K | ∃ a : A, ∃ eta : H, z = pi a (V eta)}).topologicalClosure = ⊤)
    (G : K →L[ℂ] K) (hG : ∀ a, (pi a).comp G = G.comp (pi a))
    (h0 : ∀ a, (ContinuousLinearMap.adjoint V).comp (((pi a).comp G).comp V) = 0) : G = 0 := by
  have hd := theta_dense pi V hmin
  have hG' : ∀ a x, pi a (G x) = G (pi a x) := fun a x => by
    simpa using congrArg (fun L => L x) (hG a)
  have h1 : ∀ f g, ⟪theta pi V f, G (theta pi V g)⟫_ℂ = 0 := by
    refine Sg_induct2 (P := fun f g => ⟪theta pi V f, G (theta pi V g)⟫_ℂ = 0)
      (by simp) (by simp) ?_ ?_ ?_
    · intro f1 f2 g h1 h2
      simp only [map_add, inner_add_left] at *
      rw [h1, h2]; simp
    · intro f g1 g2 h1 h2
      simp only [map_add, inner_add_right] at *
      rw [h1, h2]; simp
    · intro p c q d
      rw [theta_single, theta_single, map_smul, inner_smul_left, inner_smul_right,
        ← hG', inner_pi]
      have := congrArg (fun L => L q.2) (h0 (star p.1 * q.1))
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at this
      rw [← ContinuousLinearMap.adjoint_inner_right V, this, inner_zero_right]
      simp
  have h2 : ∀ g, G (theta pi V g) = 0 := fun g =>
    eq_zero_of_inner_range hd _ fun f => h1 f g
  ext1 x
  refine hd.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro g
  simpa using h2 g


theorem gram_of_F (T S : A →ₗ[ℂ] (H →L[ℂ] H))
    (hT : ∀ a, T a = (ContinuousLinearMap.adjoint V).comp ((pi a).comp V))
    (F : K →L[ℂ] K) (hF : (ContinuousLinearMap.id ℂ K - F).IsPositive)
    (hcomm : ∀ a, (pi a).comp F = F.comp (pi a))
    (hS : ∀ a, S a = (ContinuousLinearMap.adjoint V).comp (((pi a).comp F).comp V)) :
    GramRaw (T - S) := by
  intro n a eta
  set P := ContinuousLinearMap.id ℂ K - F with hP
  have hcomm' : ∀ a x, pi a (F x) = F (pi a x) := fun a x => by
    simpa using congrArg (fun L => L x) (hcomm a)
  have term : ∀ i j, ⟪eta i, (T - S) (star (a i) * a j) (eta j)⟫_ℂ =
      ⟪pi (a i) (V (eta i)), P (pi (a j) (V (eta j)))⟫_ℂ := by
    intro i j
    have e1 : (T - S) (star (a i) * a j) (eta j) =
        ContinuousLinearMap.adjoint V (pi (star (a i) * a j) (P (V (eta j)))) := by
      simp [LinearMap.sub_apply, hT, hS, hP, map_sub]
    rw [e1, ContinuousLinearMap.adjoint_inner_right, ← inner_pi pi (a i) (a j)]
    congr 1
    simp [hP, hcomm']
  have hsum : (∑ i, ∑ j, ⟪eta i, (T - S) (star (a i) * a j) (eta j)⟫_ℂ) =
      ⟪∑ i, pi (a i) (V (eta i)), P (∑ j, pi (a j) (V (eta j)))⟫_ℂ := by
    simp only [term, sum_inner, map_sum, inner_sum]
    exact Finset.sum_comm
  rw [hsum]
  set x := ∑ i, pi (a i) (V (eta i))
  have := (ContinuousLinearMap.isPositive_iff_complex P).1 hF x
  have e : ⟪x, P x⟫_ℂ = starRingEnd ℂ ⟪P x, x⟫_ℂ := (inner_conj_symm _ _).symm
  rw [e]
  have him : (⟪P x, x⟫_ℂ).im = 0 := by
    have h := congrArg Complex.im this.1
    simp at h
    exact h.symm
  refine ⟨by rw [Complex.conj_im, him]; simp, ?_⟩
  rw [Complex.conj_re]
  exact this.2

end Concrete
end RNAux

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P17

theorem solution {A : Type*} [CStarAlgebra A]
    (G H K : SeparableHilbertSpace) (rho : A →⋆ₐ[ℂ] HilbertEndomorphism G) (h_rho : Function.Injective rho)
    (T : A →ₗ[ℂ] HilbertEndomorphism H) (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K)
    (hT : IsNormalCP rho T) (h_dilation : ∀ a, T a = compress V (pi a))
    (h_minimal : IsMinimal pi V) (S : A →ₗ[ℂ] HilbertEndomorphism H) (hS : IsNormalCP rho S) :
    CompletelyDominated S T ↔ ∃ F : HilbertEndomorphism K, CommutesWithRepresentation pi F ∧ PositiveContraction F ∧
      (∀ a, S a = compress V ((pi a).comp F) ∧
        S a = compress V ((cfc Real.sqrt F).comp ((pi a).comp (cfc Real.sqrt F)))) ∧
      ∀ Y : HilbertEndomorphism K, CommutesWithRepresentation pi Y → (∀ a, S a = compress V ((pi a).comp Y)) → Y = F := by
  have hTd : ∀ a, T a = (ContinuousLinearMap.adjoint V).comp ((pi a).comp V) := h_dilation
  constructor
  · intro hCD
    have hSg : RNAux.GramRaw S := hS.1
    have hDg : RNAux.GramRaw (T - S) := hCD
    obtain ⟨F, hF1, hF2, hcomm, hSeq⟩ := RNAux.exists_RN pi V T S hTd h_minimal hSg hDg
    refine ⟨F, hcomm, ⟨hF1, hF2⟩, fun a => ⟨hSeq a, ?_⟩, ?_⟩
    · set s := cfc Real.sqrt F with hs
      have hsa : Commute s (pi a) := Commute.cfc_real (hcomm a).symm Real.sqrt
      have hF0 : 0 ≤ F := (ContinuousLinearMap.nonneg_iff_isPositive F).2 hF1
      have hss : s * s = F := by
        rw [hs, ← cfc_mul Real.sqrt Real.sqrt F (by fun_prop) (by fun_prop)]
        calc cfc (fun x => Real.sqrt x * Real.sqrt x) F = cfc (fun x : ℝ => x) F := by
              refine cfc_congr fun x hx => ?_
              exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hF0 hx)
          _ = F := cfc_id' ℝ F hF1.isSelfAdjoint
      have : s.comp ((pi a).comp s) = (pi a).comp F := by
        have e1 : s.comp ((pi a).comp s) = s * (pi a * s) := rfl
        have e2 : (pi a).comp F = pi a * F := rfl
        rw [e1, e2, ← hss, ← mul_assoc, hsa.eq, mul_assoc]
      rw [this]; exact hSeq a
    · intro Y hY hYS
      have h0 := RNAux.commutant_zero pi V h_minimal (Y - F) (fun a => by
          rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp, hY a, hcomm a]) (fun a => by
          have e1 := hYS a
          have e2 := hSeq a
          have : (ContinuousLinearMap.adjoint V).comp (((pi a).comp (Y - F)).comp V) =
              compress V ((pi a).comp Y) - compress V ((pi a).comp F) := by
            simp only [compress, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
          rw [this, ← e1, sub_eq_zero]; exact e2)
      exact sub_eq_zero.mp h0
  · rintro ⟨F, hcomm, ⟨hF1, hF2⟩, hSeq, -⟩
    exact RNAux.gram_of_F pi V T S hTd F hF2 hcomm (fun a => (hSeq a).1)

end
