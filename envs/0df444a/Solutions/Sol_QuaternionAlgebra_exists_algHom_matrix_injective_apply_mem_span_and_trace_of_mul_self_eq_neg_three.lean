-- Prove2me | solution 1 for QuaternionAlgebra.exists_algHom_matrix_injective_apply_mem_span_and_trace_of_mul_self_eq_neg_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/7441beab-5b2e-5a99-9653-22239b0078fa

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_algHom_matrix_injective_apply_mem_span_and_trace_of_mul_self_eq_neg_three

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false

open scoped Quaternion NumberField
open QuaternionAlgebra

abbrev K₃ : Type := CyclotomicField 3 ℚ
scoped instance K₃.isCycl : IsCyclotomicExtension {3} ℚ K₃ := CyclotomicField.isCyclotomicExtension 3 ℚ

p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_algHom_matrix_injective_apply_mem_span_and_trace_of_mul_self_eq_neg_three.K₃"
namespace D2Q

variable {a b : ℚ}

noncomputable def zeta3 : K₃ := IsCyclotomicExtension.zeta 3 ℚ K₃
theorem zeta3_spec : IsPrimitiveRoot zeta3 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K₃

noncomputable def pb : PowerBasis ℚ K₃ := IsPrimitiveRoot.powerBasis ℚ zeta3_spec
theorem pb_gen : pb.gen = zeta3 := IsPrimitiveRoot.powerBasis_gen ℚ zeta3_spec
theorem minpoly_gen : minpoly ℚ pb.gen = Polynomial.X ^ 2 + Polynomial.X + 1 := by
  rw [pb_gen, ← Polynomial.cyclotomic_eq_minpoly_rat zeta3_spec (by norm_num), Polynomial.cyclotomic_three]

theorem finrank_K₃ : Module.finrank ℚ K₃ = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 3) K₃ (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  rfl

noncomputable def theta (ξ : ℍ[ℚ,a,b]) : ℍ[ℚ,a,b] := (2 : ℚ)⁻¹ • (ξ - 1)

theorem theta_spec (ξ : ℍ[ℚ,a,b]) (hξ : ξ * ξ = algebraMap ℚ ℍ[ℚ, a, b] (-3)) :
    theta ξ * theta ξ + theta ξ + 1 = 0 := by
  have h4 : (4 : ℚ) • (theta ξ * theta ξ + theta ξ + 1) = 0 := by
    simp only [theta, smul_add, mul_sub, sub_mul, smul_sub, mul_smul_comm, smul_mul_assoc, smul_smul, hξ, one_mul,
      mul_one]
    rw [Algebra.algebraMap_eq_smul_one]
    module
  exact (smul_eq_zero_iff_right (by norm_num : (4:ℚ) ≠ 0)).1 h4

noncomputable def iota (ξ : ℍ[ℚ,a,b]) (hξ : ξ * ξ = algebraMap ℚ ℍ[ℚ, a, b] (-3)) : K₃ →ₐ[ℚ] ℍ[ℚ,a,b] :=
  pb.lift (theta ξ) (by
    rw [minpoly_gen]
    simp only [map_add, map_pow, map_one, Polynomial.aeval_X]
    rw [pow_two]; exact theta_spec ξ hξ)

noncomputable def modK (ι : K₃ →ₐ[ℚ] ℍ[ℚ,a,b]) : Module K₃ ℍ[ℚ,a,b] :=
  Module.compHom ℍ[ℚ,a,b] (ι.toRingHom.toOpposite fun x y => (Commute.all x y).map ι.toRingHom)

theorem modK_smul_def (ι : K₃ →ₐ[ℚ] ℍ[ℚ,a,b]) (k : K₃) (x : ℍ[ℚ,a,b]) :
    (letI := modK ι; k • x) = x * ι k := rfl

theorem ist (ι : K₃ →ₐ[ℚ] ℍ[ℚ,a,b]) : @IsScalarTower ℚ K₃ ℍ[ℚ,a,b] _ (modK ι).toSMul _ := by
  letI := modK ι
  constructor
  intro q k x
  show x * ι (q • k) = q • (x * ι k)
  rw [map_smul, mul_smul_comm]

section rep

theorem exists_algHom_injective (ξ : ℍ[ℚ,a,b]) (hξ : ξ * ξ = algebraMap ℚ ℍ[ℚ, a, b] (-3))
    (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x) :
    ∃ ρ : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₃, Function.Injective ρ := by
  classical
  let ι : K₃ →ₐ[ℚ] ℍ[ℚ,a,b] := iota ξ hξ
  letI instM : Module K₃ ℍ[ℚ,a,b] := modK ι
  haveI instT : IsScalarTower ℚ K₃ ℍ[ℚ,a,b] := ist ι
  haveI : Module.Finite K₃ ℍ[ℚ,a,b] := Module.Finite.of_restrictScalars_finite ℚ K₃ ℍ[ℚ,a,b]
  have hrank : Module.finrank K₃ ℍ[ℚ,a,b] = 2 := by
    have h := Module.finrank_mul_finrank ℚ K₃ ℍ[ℚ,a,b]
    rw [finrank_K₃, QuaternionAlgebra.finrank_eq_four] at h
    omega
  let bs : Module.Basis (Fin 2) K₃ ℍ[ℚ,a,b] := Module.finBasisOfFinrankEq K₃ ℍ[ℚ,a,b] hrank

  let L : ℍ[ℚ,a,b] → (ℍ[ℚ,a,b] →ₗ[K₃] ℍ[ℚ,a,b]) := fun m =>
    { toFun := fun x => m * x
      map_add' := fun x y => mul_add m x y
      map_smul' := fun k x => by
        change m * (x * ι k) = (m * x) * ι k
        rw [mul_assoc] }
  have L_apply : ∀ m x, L m x = m * x := fun m x => rfl
  have L_one : L 1 = LinearMap.id := LinearMap.ext fun x => by rw [L_apply, one_mul]; rfl
  have L_mul : ∀ m n, L (m * n) = L m ∘ₗ L n := fun m n => LinearMap.ext fun x => by
    simp only [L_apply, LinearMap.comp_apply, mul_assoc]
  have L_add : ∀ m n, L (m + n) = L m + L n := fun m n => LinearMap.ext fun x => by
    simp only [L_apply, LinearMap.add_apply, add_mul]
  have L_zero : L 0 = 0 := LinearMap.ext fun x => by simp only [L_apply, LinearMap.zero_apply, zero_mul]
  have L_alg : ∀ q : ℚ, L (algebraMap ℚ ℍ[ℚ,a,b] q) = algebraMap ℚ K₃ q • LinearMap.id := fun q =>
    LinearMap.ext fun x => by
      rw [L_apply, LinearMap.smul_apply, LinearMap.id_apply]
      change algebraMap ℚ ℍ[ℚ,a,b] q * x = x * ι (algebraMap ℚ K₃ q)
      rw [AlgHom.commutes, Algebra.commutes]
  let ρ : ℍ[ℚ,a,b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₃ :=
    { toFun := fun m => LinearMap.toMatrix bs bs (L m)
      map_one' := by simp only [L_one, LinearMap.toMatrix_id]
      map_mul' := fun m n => by simp only [L_mul, LinearMap.toMatrix_comp bs bs bs]
      map_zero' := by simp only [L_zero, map_zero]
      map_add' := fun m n => by simp only [L_add, map_add]
      commutes' := fun q => by
        simp only [L_alg, map_smul, LinearMap.toMatrix_id]
        first
          | rw [algebraMap_smul, Algebra.algebraMap_eq_smul_one]
          | rw [smul_one_smul, Algebra.algebraMap_eq_smul_one] }
  refine ⟨ρ, (injective_iff_map_eq_zero ρ).2 fun m hm => ?_⟩
  have h1 : L m = 0 := (LinearMap.toMatrix bs bs).map_eq_zero_iff.1 hm
  have h2 : L m 1 = 0 := by rw [h1]; rfl
  rwa [L_apply, mul_one] at h2

end rep
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_algHom_matrix_injective_apply_mem_span_and_trace_of_mul_self_eq_neg_three.K₃"

theorem span_pair_mul_mem {K : Type} [Field K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0) {x y : K}
    (hx : x ∈ Submodule.span ℤ ({1, ω} : Set K)) (hy : y ∈ Submodule.span ℤ ({1, ω} : Set K)) :
    x * y ∈ Submodule.span ℤ ({1, ω} : Set K) := by
  rw [Submodule.mem_span_pair] at hx hy ⊢
  obtain ⟨p, q, rfl⟩ := hx
  obtain ⟨r, s, rfl⟩ := hy
  have hω' : ω * ω = -ω - 1 := by rw [← pow_two]; linear_combination hω
  refine ⟨p * r - q * s, p * s + q * r - q * s, ?_⟩
  simp only [zsmul_eq_mul, smul_eq_mul]
  push_cast
  linear_combination (-(q : K) * s) * hω'

theorem exists_algHom_map_integral (K : Type) [Field K] [CharZero K] [Algebra ℚ K]
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ φ : K₃ →ₐ[ℚ] K, Function.Injective φ ∧
      ∀ x : K₃, x ∈ integralClosure ℤ K₃ → φ x ∈ Submodule.span ℤ ({1, ω} : Set K) := by
  classical
  have hgen : Polynomial.aeval ω (minpoly ℚ pb.gen) = 0 := by
    rw [minpoly_gen]
    simp only [map_add, map_pow, map_one, Polynomial.aeval_X]
    exact hω
  let φ : K₃ →ₐ[ℚ] K := pb.lift ω hgen
  have hφζ : φ zeta3 = ω := by rw [← pb_gen]; exact pb.lift_gen ω hgen
  refine ⟨φ, φ.toRingHom.injective, fun x hx => ?_⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hIC : IsIntegralClosure (Algebra.adjoin ℤ ({zeta3} : Set K₃)) ℤ K₃ :=
    IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime (p := 3) zeta3_spec
  have hxint : IsIntegral ℤ x := hx
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := Algebra.adjoin ℤ ({zeta3} : Set K₃))).1 hxint
  have hx' : x ∈ Algebra.adjoin ℤ ({zeta3} : Set K₃) := by rw [← hy]; exact y.2
  clear hy hxint hx

  induction hx' using Algebra.adjoin_induction with
  | mem z hz =>
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [hφζ]
    exact Submodule.subset_span (by simp)
  | algebraMap r =>
    have : φ (algebraMap ℤ K₃ r) = (r : ℤ) • (1 : K) := by
      rw [eq_intCast, map_intCast, zsmul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ r (Submodule.subset_span (by simp))
  | add z w _ _ hz hw => rw [map_add]; exact Submodule.add_mem _ hz hw
  | mul z w _ _ hz hw => rw [map_mul]; exact span_pair_mul_mem ω hω hz hw

theorem exists_matrix_forall_mem_iff_forall_mulVec_mem
    (F : Type) [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)]
    (M : Submodule ℤ (Fin 2 → F)) (hfg : M.FG)
    (hspan : Submodule.span ℚ (M : Set (Fin 2 → F)) = ⊤)
    (hM : ∀ m ∈ M, ∀ o : F, o ∈ integralClosure ℤ F → (fun i => m i * o) ∈ M) :
    ∃ γ γ' : Matrix (Fin 2) (Fin 2) F, γ * γ' = 1 ∧ γ' * γ = 1 ∧
      ∀ x : Fin 2 → F, x ∈ M ↔ ∀ i, (γ'.mulVec x) i ∈ integralClosure ℤ F := by
  classical

  have smul_eq : ∀ (r : 𝓞 F) (x : Fin 2 → F), r • x = fun i => x i * (r : F) := by
    intro r x; funext i
    rw [Pi.smul_apply, Algebra.smul_def, mul_comm]
  let M' : Submodule (𝓞 F) (Fin 2 → F) :=
    { carrier := M
      add_mem' := fun hx hy => M.add_mem hx hy
      zero_mem' := M.zero_mem
      smul_mem' := fun r x hx => by
        show r • x ∈ M
        rw [smul_eq]; exact hM x hx r r.2 }
  have memM' : ∀ x, x ∈ M' ↔ x ∈ M := fun x => Iff.rfl

  haveI hfin : Module.Finite (𝓞 F) M' := by
    rw [Module.Finite.iff_fg]
    obtain ⟨s, hs⟩ := hfg
    refine ⟨s, le_antisymm ?_ ?_⟩
    · exact Submodule.span_le.2 fun x hx => (memM' x).2 (hs ▸ Submodule.subset_span hx)
    · intro x (hx : x ∈ M)
      rw [← hs] at hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span hy
      | zero => exact Submodule.zero_mem _
      | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
      | smul n y _ hy => exact zsmul_mem hy n
  haveI : Module.IsTorsionFree (𝓞 F) M' := inferInstance
  haveI : Module.Free (𝓞 F) M' := Module.free_of_finite_type_torsion_free'

  let ιM := Module.Free.ChooseBasisIndex (𝓞 F) M'
  let bM : Module.Basis ιM (𝓞 F) M' := Module.Free.chooseBasis (𝓞 F) M'
  haveI : Finite ιM := Module.Finite.finite_basis bM
  letI : Fintype ιM := Fintype.ofFinite ιM
  let v : ιM → (Fin 2 → F) := fun i => (bM i : Fin 2 → F)
  have hvR : LinearIndependent (𝓞 F) v :=
    bM.linearIndependent.map' M'.subtype (Submodule.ker_subtype M')
  have hvF : LinearIndependent F v := (LinearIndependent.iff_fractionRing (𝓞 F) F).1 hvR

  have coe_smul : ∀ (r : 𝓞 F) (y : Fin 2 → F), r • y = (r : F) • y := fun r y =>
    (IsScalarTower.algebraMap_smul F r y).symm
  have repr_eq : ∀ (x : Fin 2 → F) (hx : x ∈ M),
      x = ∑ i, ((bM.repr ⟨x, hx⟩ i : 𝓞 F) : F) • v i := by
    intro x hx
    have h := congrArg (fun y : M' => (y : Fin 2 → F)) (bM.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, coe_smul] at h
    exact h.symm

  have hMle : (M : Set (Fin 2 → F)) ⊆ Submodule.span F (Set.range v) := by
    intro x hx
    rw [repr_eq x hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hvsp : ⊤ ≤ Submodule.span F (Set.range v) := by
    intro y _
    have hy : y ∈ Submodule.span ℚ (M : Set (Fin 2 → F)) := by rw [hspan]; trivial
    have : Submodule.span ℚ (M : Set (Fin 2 → F)) ≤
        (Submodule.span F (Set.range v)).restrictScalars ℚ := by
      rw [Submodule.span_le]
      exact hMle
    exact this hy
  let bF : Module.Basis ιM F (Fin 2 → F) := Module.Basis.mk hvF hvsp
  have bF_apply : ∀ i, bF i = v i := fun i => Module.Basis.mk_apply hvF hvsp i

  have hcard : Fintype.card ιM = 2 := by
    have h := Module.finrank_eq_card_basis bF
    rw [Module.finrank_fin_fun] at h
    exact h.symm
  let e : ιM ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  let bF2 : Module.Basis (Fin 2) F (Fin 2 → F) := bF.reindex e
  let bM2 : Module.Basis (Fin 2) (𝓞 F) M' := bM.reindex e
  have hb : ∀ l, (bM2 l : Fin 2 → F) = bF2 l := by
    intro l
    simp only [bM2, bF2, Module.Basis.reindex_apply, bF_apply, v]

  let P := Pi.basisFun F (Fin 2)
  let γ : Matrix (Fin 2) (Fin 2) F := P.toMatrix bF2
  let γ' : Matrix (Fin 2) (Fin 2) F := bF2.toMatrix P
  have h1 : γ * γ' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip P bF2
  have h2 : γ' * γ = 1 := Module.Basis.toMatrix_mul_toMatrix_flip bF2 P
  have hγ' : ∀ x : Fin 2 → F, γ'.mulVec x = bF2.repr x := by
    intro x
    have hx : ⇑(P.repr x) = x := funext fun i => Pi.basisFun_repr F (Fin 2) x i
    have := Module.Basis.toMatrix_mulVec_repr P bF2 x
    rwa [hx] at this
  refine ⟨γ, γ', h1, h2, fun x => ?_⟩
  rw [hγ']
  constructor
  · intro hx i
    set c := bM2.repr ⟨x, hx⟩ with hc
    have hsum : x = ∑ l, ((c l : 𝓞 F) : F) • bF2 l := by
      have h := congrArg (fun y : M' => (y : Fin 2 → F)) (bM2.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, coe_smul, hb] at h
      exact h.symm
    have hrepr : ⇑(bF2.repr x) = fun l => ((c l : 𝓞 F) : F) := by
      conv_lhs => rw [hsum]
      exact bF2.repr_sum_self _
    rw [hrepr]
    exact (c i).2
  · intro hx
    rw [← bF2.sum_repr x]
    refine M.sum_mem fun l _ => ?_
    let r : 𝓞 F := ⟨bF2.repr x l, hx l⟩
    have hr : (r : F) = bF2.repr x l := rfl
    have : (bF2.repr x l) • bF2 l = ((r • bM2 l : M') : Fin 2 → F) := by
      rw [Submodule.coe_smul, coe_smul, hb, hr]
    rw [this]
    exact (r • bM2 l).2

end D2Q
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_algHom_matrix_injective_apply_mem_span_and_trace_of_mul_self_eq_neg_three.K₃"

namespace P2mIntegral

variable {A : Type*} [Ring A]

def conjAlgHom {R : Type*} [CommSemiring R] [Algebra R A] (γ γ' : A) (h : γ * γ' = 1) (h' : γ' * γ = 1) :
    A →ₐ[R] A where
  toFun x := γ' * x * γ
  map_one' := by rw [mul_one, h']
  map_mul' x y := by
    calc γ' * (x * y) * γ = γ' * x * (γ * γ') * y * γ := by rw [h]; noncomm_ring
      _ = γ' * x * γ * (γ' * y * γ) := by noncomm_ring
  map_zero' := by rw [mul_zero, zero_mul]
  map_add' x y := by rw [mul_add, add_mul]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, h']

theorem conjAlgHom_apply {R : Type*} [CommSemiring R] [Algebra R A] (γ γ' : A) (h : γ * γ' = 1) (h' : γ' * γ = 1)
    (x : A) : conjAlgHom (R := R) γ γ' h h' x = γ' * x * γ := rfl

theorem conjAlgHom_injective {R : Type*} [CommSemiring R] [Algebra R A] (γ γ' : A) (h : γ * γ' = 1)
    (h' : γ' * γ = 1) : Function.Injective (conjAlgHom (R := R) γ γ' h h') := by
  intro x y hxy
  rw [conjAlgHom_apply, conjAlgHom_apply] at hxy
  have := congrArg (fun z => γ * z * γ') hxy
  calc x = (γ * γ') * x * (γ * γ') := by rw [h, one_mul, mul_one]
    _ = γ * (γ' * x * γ) * γ' := by noncomm_ring
    _ = γ * (γ' * y * γ) * γ' := this
    _ = (γ * γ') * y * (γ * γ') := by noncomm_ring
    _ = y := by rw [h, one_mul, mul_one]

theorem mul_mul_apply_eq_mulVec (γ' X γ : Matrix (Fin 2) (Fin 2) A) (i l : Fin 2) :
    (γ' * X * γ) i l = (γ'.mulVec (X.mulVec (γ.mulVec (Pi.single l 1)))) i := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

end P2mIntegral
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_algHom_matrix_injective_apply_mem_span_and_trace_of_mul_self_eq_neg_three.K₃"

namespace D2A

noncomputable abbrev OK : Subalgebra ℤ K₃ := integralClosure ℤ K₃

theorem zeta3 : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K₃) 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K₃

theorem OK_fg : (OK).toSubmodule.FG := by
  have h2 : (⊤ : Submodule ℤ ↥((OK).toSubmodule)).FG := Module.Finite.fg_top (R := ℤ) (M := 𝓞 K₃)
  exact (Submodule.fg_top _).mp h2

theorem OK_span : Submodule.span ℚ ((OK).toSubmodule : Set K₃) = ⊤ := by
  apply top_unique
  have hb := (IsPrimitiveRoot.powerBasis ℚ zeta3).basis.span_eq
  rw [← hb]
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  rw [PowerBasis.coe_basis, IsPrimitiveRoot.powerBasis_gen]
  show IsCyclotomicExtension.zeta 3 ℚ K₃ ^ (i : ℕ) ∈ integralClosure ℤ K₃
  exact (zeta3.isIntegral (by norm_num)).pow _

open P2mIntegral in

theorem exists_conj {a b : ℚ} (ρ : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₃) (hρ : Function.Injective ρ)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) :
    ∃ j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₃, Function.Injective j ∧
      (∀ m ∈ Λ, ∀ i l : Fin 2, j m i l ∈ OK) ∧ ∀ m, (j m).trace = (ρ m).trace := by
  set O : Submodule ℤ K₃ := (OK).toSubmodule with hOdef
  have hOfg : O.FG := OK_fg
  have hOspan : Submodule.span ℚ (O : Set K₃) = ⊤ := OK_span

  classical

  let gen : ℍ[ℚ, a, b] → Fin 2 → K₃ → (Fin 2 → K₃) := fun l k o =>
    (ρ l).mulVec (Pi.single k o)
  let S : Set (Fin 2 → K₃) := {x | ∃ l ∈ Λ, ∃ k : Fin 2, ∃ o ∈ O, x = gen l k o}
  let M : Submodule ℤ (Fin 2 → K₃) := Submodule.span ℤ S
  have gen_mem : ∀ l ∈ Λ, ∀ (k : Fin 2), ∀ o ∈ O, gen l k o ∈ M := fun l hl k o ho =>
    Submodule.subset_span ⟨l, hl, k, o, ho, rfl⟩

  have gen_add_left : ∀ (l l' : ℍ[ℚ, a, b]) (k : Fin 2) (o : K₃),
      gen (l + l') k o = gen l k o + gen l' k o := fun l l' k o => by
    simp only [gen, map_add, Matrix.add_mulVec]
  have gen_smul_left : ∀ (n : ℤ) (l : ℍ[ℚ, a, b]) (k : Fin 2) (o : K₃),
      gen (n • l) k o = n • gen l k o := fun n l k o => by
    simp only [gen, map_zsmul, Matrix.smul_mulVec]
  have gen_add_right : ∀ (l : ℍ[ℚ, a, b]) (k : Fin 2) (o o' : K₃),
      gen l k (o + o') = gen l k o + gen l k o' := fun l k o o' => by
    simp only [gen, Pi.single_add, Matrix.mulVec_add]
  have gen_smul_right : ∀ (n : ℤ) (l : ℍ[ℚ, a, b]) (k : Fin 2) (o : K₃),
      gen l k (n • o) = n • gen l k o := fun n l k o => by
    simp only [gen, Pi.single_smul, Matrix.mulVec_smul]

  have mul_right : ∀ (l : ℍ[ℚ, a, b]) (k : Fin 2) (o o' : K₃),
      (fun i => gen l k o i * o') = gen l k (o * o') := fun l k o o' => by
    funext i
    simp only [gen, Matrix.mulVec, dotProduct, Finset.sum_mul, Pi.single_apply, mul_ite, mul_zero, ite_mul,
      zero_mul, mul_assoc]
  have hM : ∀ m ∈ M, ∀ o ∈ O, (fun i => m i * o) ∈ M := by
    intro m hm o ho
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, k, o₁, ho₁, rfl⟩ := hx
      rw [mul_right]
      exact gen_mem l hl k _ (OK.mul_mem ho₁ ho)
    | zero =>
      have : (fun i => (0 : Fin 2 → K₃) i * o) = 0 := by funext i; simp
      rw [this]; exact M.zero_mem
    | add x y _ _ hx hy =>
      have : (fun i => (x + y) i * o) = (fun i => x i * o) + fun i => y i * o := by
        funext i; simp [add_mul]
      rw [this]; exact M.add_mem hx hy
    | smul n x _ hx =>
      have : (fun i => (n • x) i * o) = n • fun i => x i * o := by
        funext i; simp [mul_assoc]
      rw [this]; exact M.smul_mem n hx

  have mul_left : ∀ (l l' : ℍ[ℚ, a, b]) (k : Fin 2) (o : K₃),
      (ρ l').mulVec (gen l k o) = gen (l' * l) k o := fun l l' k o => by
    simp only [gen, map_mul, Matrix.mulVec_mulVec]
  have hML : ∀ m ∈ M, ∀ l' ∈ Λ, (ρ l').mulVec m ∈ M := by
    intro m hm l' hl'
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, k, o₁, ho₁, rfl⟩ := hx
      rw [mul_left]
      exact gen_mem _ (hΛ.mul_mem hl' hl) k o₁ ho₁
    | zero => rw [Matrix.mulVec_zero]; exact M.zero_mem
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact M.add_mem hx hy
    | smul n x _ hx => rw [Matrix.mulVec_smul]; exact M.smul_mem n hx

  have hfg : M.FG := by
    obtain ⟨sΛ, hsΛ⟩ := hΛ.fg
    obtain ⟨sO, hsO⟩ := hOfg
    let T : Finset (Fin 2 → K₃) :=
      ((sΛ ×ˢ (Finset.univ : Finset (Fin 2))) ×ˢ sO).image fun p => gen p.1.1 p.1.2 p.2
    refine ⟨T, le_antisymm ?_ ?_⟩
    · refine Submodule.span_le.2 ?_
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
      obtain ⟨hp11, -⟩ := Finset.mem_product.1 hp1
      exact gen_mem _ (hsΛ ▸ Submodule.subset_span hp11) _ _ (hsO ▸ Submodule.subset_span hp2)
    · refine Submodule.span_le.2 ?_
      rintro x ⟨l, hl, k, o, ho, rfl⟩

      have step1 : ∀ o' ∈ sO, ∀ l' ∈ Λ, gen l' k o' ∈ Submodule.span ℤ (T : Set (Fin 2 → K₃)) := by
        intro o' ho' l' hl'
        rw [← hsΛ] at hl'
        induction hl' using Submodule.span_induction with
        | mem l₀ hl₀ =>
          refine Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2 ⟨((l₀, k), o'), ?_, rfl⟩))
          exact Finset.mem_product.2 ⟨Finset.mem_product.2 ⟨hl₀, Finset.mem_univ _⟩, ho'⟩
        | zero =>
          have : gen 0 k o' = 0 := by simp only [gen, map_zero, Matrix.zero_mulVec]
          rw [this]; exact Submodule.zero_mem _
        | add u w _ _ hu hw => rw [gen_add_left]; exact Submodule.add_mem _ hu hw
        | smul n u _ hu => rw [gen_smul_left]; exact Submodule.smul_mem _ n hu
      have step2 : ∀ o' ∈ O, gen l k o' ∈ Submodule.span ℤ (T : Set (Fin 2 → K₃)) := by
        intro o' ho'
        rw [← hsO] at ho'
        induction ho' using Submodule.span_induction with
        | mem o₀ ho₀ => exact step1 o₀ ho₀ l hl
        | zero =>
          have : gen l k 0 = 0 := by simp only [gen, Pi.single_zero, Matrix.mulVec_zero]
          rw [this]; exact Submodule.zero_mem _
        | add u w _ _ hu hw => rw [gen_add_right]; exact Submodule.add_mem _ hu hw
        | smul n u _ hu =>
          convert Submodule.smul_mem _ n hu using 1
          exact gen_smul_right n l k u
      exact step2 o ho

  have single_mem : ∀ (k : Fin 2), ∀ o ∈ O, Pi.single k o ∈ M := fun k o ho => by
    have := gen_mem 1 hΛ.one_mem k o ho
    simpa only [gen, map_one, Matrix.one_mulVec] using this
  have hspan : Submodule.span ℚ (M : Set (Fin 2 → K₃)) = ⊤ := by
    refine top_unique fun x _ => ?_
    have hx : x = ∑ k : Fin 2, Pi.single k (x k) := by
      funext i
      rw [Finset.sum_apply, Fin.sum_univ_two]
      fin_cases i <;> simp
    rw [hx]
    refine Submodule.sum_mem _ fun k _ => ?_

    have hxk : x k ∈ Submodule.span ℚ (O : Set K₃) := by rw [hOspan]; trivial
    generalize x k = y at hxk
    induction hxk using Submodule.span_induction with
    | mem o ho => exact Submodule.subset_span (single_mem k o ho)
    | zero => rw [Pi.single_zero]; exact Submodule.zero_mem _
    | add u w _ _ hu hw => rw [Pi.single_add]; exact Submodule.add_mem _ hu hw
    | smul r u _ hu => rw [Pi.single_smul]; exact Submodule.smul_mem _ r hu

  haveI : IsPrincipalIdealRing (𝓞 K₃) := IsCyclotomicExtension.Rat.three_pid K₃
  obtain ⟨γ, γ', hγγ', hγ'γ, hmem⟩ :=
    D2Q.exists_matrix_forall_mem_iff_forall_mulVec_mem K₃ M hfg hspan (fun m hm o ho => hM m hm o ho)

  refine ⟨(conjAlgHom (R := ℚ) γ γ' hγγ' hγ'γ).comp ρ, (conjAlgHom_injective (R := ℚ) γ γ' hγγ' hγ'γ).comp hρ,
    fun m hm i l => ?_, fun m => ?_⟩
  swap
  · rw [AlgHom.comp_apply, conjAlgHom_apply, Matrix.trace_mul_cycle, hγγ', one_mul]
  rw [AlgHom.comp_apply, conjAlgHom_apply, mul_mul_apply_eq_mulVec]
  have hcol : γ.mulVec (Pi.single l 1) ∈ M := by
    rw [hmem, Matrix.mulVec_mulVec, hγ'γ, Matrix.one_mulVec]
    intro i
    by_cases hil : i = l
    · subst hil; rw [Pi.single_eq_same]; exact OK.one_mem
    · rw [Pi.single_eq_of_ne hil]; exact OK.zero_mem
  exact (hmem _).1 (hML _ hcol m hm) i

end D2A
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_algHom_matrix_injective_apply_mem_span_and_trace_of_mul_self_eq_neg_three.K₃"

namespace D2A

theorem sq_eq_trace_smul_sub_det_smul {F : Type} [CommRing F] (X : Matrix (Fin 2) (Fin 2) F) :
    X * X = X.trace • X - X.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply] <;> ring

theorem eq_algebraMap_re_of_forall_comm {a b : ℚ} (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (m : ℍ[ℚ, a, b]) (hcomm : ∀ y : ℍ[ℚ, a, b], m * y = y * m) : m = algebraMap ℚ ℍ[ℚ, a, b] m.re := by
  have hane : a ≠ 0 := by
    intro ha
    have hi : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) ≠ 0 := by
      intro h; have := congrArg QuaternionAlgebra.imI h; simp at this
    have hii : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 1, 0, 0⟩ = 0 := by ext <;> simp [ha]
    have hu := (hdiv _ hi).mul (hdiv _ hi)
    rw [hii] at hu
    exact not_isUnit_zero hu
  have hbne : b ≠ 0 := by
    intro hb
    have hj : (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) ≠ 0 := by
      intro h; have := congrArg QuaternionAlgebra.imJ h; simp at this
    have hjj : (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 0, 1, 0⟩ = 0 := by ext <;> simp [hb]
    have hu := (hdiv _ hj).mul (hdiv _ hj)
    rw [hjj] at hu
    exact not_isUnit_zero hu
  have h1 := hcomm ⟨0, 1, 0, 0⟩
  have h2 := hcomm ⟨0, 0, 1, 0⟩
  obtain ⟨m₀, m₁, m₂, m₃⟩ := m
  have e1 := congrArg QuaternionAlgebra.imK h1
  have e2 := congrArg QuaternionAlgebra.imJ h1
  have e3 := congrArg QuaternionAlgebra.imK h2
  have e4 := congrArg QuaternionAlgebra.imI h2
  simp at e1 e2 e3 e4
  have hm₁ : m₁ = 0 := by linarith
  have hm₂ : m₂ = 0 := by linarith
  have hm₃ : m₃ = 0 := by
    have : a * m₃ = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hane
  ext <;> simp [hm₁, hm₂, hm₃]

theorem trace_eq {F : Type} [Field F] [Algebra ℚ F] {a b : ℚ}
    (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (ρ : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) F) (hρ : Function.Injective ρ)
    (m : ℍ[ℚ, a, b]) (t : ℚ) (hm : m + star m = algebraMap ℚ ℍ[ℚ, a, b] t) :
    (ρ m) 0 0 + (ρ m) 1 1 = algebraMap ℚ F t := by
  classical

  set n : ℚ := (m * star m).re with hn
  have hmn : m * star m = algebraMap ℚ ℍ[ℚ, a, b] n := by
    rw [hn]; exact QuaternionAlgebra.mul_star_eq_coe m
  have hstar : star m = algebraMap ℚ ℍ[ℚ, a, b] t - m := by rw [← hm]; abel
  have hsqB : m * m = t • m - n • (1 : ℍ[ℚ, a, b]) := by
    have h1 : m * (algebraMap ℚ ℍ[ℚ, a, b] t - m) = algebraMap ℚ ℍ[ℚ, a, b] n := by rw [← hstar, hmn]
    rw [mul_sub, ← Algebra.commutes, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one, sub_eq_iff_eq_add] at h1
    rw [h1]; abel
  set X := ρ m with hX
  have hsq : X * X = t • X - n • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg ρ hsqB
    rw [map_mul, map_sub, map_smul, map_smul, map_one] at this
    exact this
  have hch := sq_eq_trace_smul_sub_det_smul X
  have key : (X.trace - algebraMap ℚ F t) • X = (X.det - algebraMap ℚ F n) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [sub_smul, sub_smul, algebraMap_smul, algebraMap_smul]
    have e1 : X.trace • X - X.det • (1 : Matrix (Fin 2) (Fin 2) F) = t • X - n • 1 := hch.symm.trans hsq
    exact sub_eq_sub_iff_sub_eq_sub.mp e1
  by_cases htr : X.trace - algebraMap ℚ F t = 0
  · rw [← Matrix.trace_fin_two]; exact sub_eq_zero.mp htr
  · exfalso
    set c : F := (X.trace - algebraMap ℚ F t)⁻¹ * (X.det - algebraMap ℚ F n) with hc
    have hXc : X = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [hc, mul_smul, ← key, smul_smul, inv_mul_cancel₀ htr, one_smul]
    have hcomm : ∀ y : ℍ[ℚ, a, b], m * y = y * m := by
      intro y
      apply hρ
      rw [map_mul, map_mul, ← hX, hXc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
    have hmre := eq_algebraMap_re_of_forall_comm hdiv m hcomm

    have ht' : t = 2 * m.re := by
      have := congrArg QuaternionAlgebra.re hm
      simp at this
      linarith
    apply htr
    rw [hX, hmre, AlgHom.commutes, Matrix.trace_fin_two, Matrix.algebraMap_matrix_apply,
      Matrix.algebraMap_matrix_apply, sub_eq_zero, ht', map_mul, map_ofNat]
    simp [two_mul]

end D2A
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_algHom_matrix_injective_apply_mem_span_and_trace_of_mul_self_eq_neg_three.K₃"

theorem solution
    (K : Type) [Field K] [CharZero K] [Algebra ℚ K] (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    (O : Submodule ℤ K) (hO : O = Submodule.span ℤ ({1, ω} : Set K))
    {a b : ℚ} (ξ : ℍ[ℚ, a, b]) (hξ : ξ * ξ = algebraMap ℚ ℍ[ℚ, a, b] (-3))
    (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) :
    ∃ j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K, Function.Injective j ∧
      (∀ m ∈ Λ, ∀ i l : Fin 2, j m i l ∈ O) ∧
      ∀ (m : ℍ[ℚ, a, b]) (t : ℚ), m + star m = algebraMap ℚ ℍ[ℚ, a, b] t →
        j m 0 0 + j m 1 1 = algebraMap ℚ K t := by
  classical
  obtain ⟨ρ, hρ⟩ := D2Q.exists_algHom_injective ξ hξ hdiv
  obtain ⟨j', hj'inj, hj'int, hj'tr⟩ := D2A.exists_conj ρ hρ Λ hΛ
  obtain ⟨φ, hφinj, hφ⟩ := D2Q.exists_algHom_map_integral K ω hω
  refine ⟨φ.mapMatrix.comp j', ?_, ?_, ?_⟩
  · intro x y hxy
    apply hj'inj
    ext i l
    have := congrFun (congrFun hxy i) l
    simp only [AlgHom.comp_apply, AlgHom.mapMatrix_apply, Matrix.map_apply] at this
    exact hφinj this
  · intro m hm i l
    rw [hO]
    simp only [AlgHom.comp_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
    exact hφ _ (hj'int m hm i l)
  · intro m t hmt
    simp only [AlgHom.comp_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
    rw [← map_add, ← Matrix.trace_fin_two, hj'tr m, Matrix.trace_fin_two, D2A.trace_eq hdiv ρ hρ m t hmt,
      AlgHom.commutes]

end S_QuaternionAlgebra_exists_algHom_matrix_injective_apply_mem_span_and_trace_of_mul_self_eq_neg_three
end P2MW
export P2MW.S_QuaternionAlgebra_exists_algHom_matrix_injective_apply_mem_span_and_trace_of_mul_self_eq_neg_three (solution)
