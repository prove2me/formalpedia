-- Prove2me | solution 1 for PDivisibleGroup.exists_nsmul_eq_of_forall_isNilpotent_cpointsProj_one_of_isIntegral_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ba3b938b-ea04-51b7-a517-89b9daa014f8

import Mathlib
import Definitions.Def_PDivisibleGroup_CompletedPoints
import Theorems.Thm_PDivisibleGroup_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk
import Theorems.Thm_PadicAlgCl_exists_forall_ringHom_apply_algebraMap_eq_of_free_of_ker_eq_span_pow
import Theorems.Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_nsmul_eq_of_forall_isNilpotent_cpointsProj_one_of_isIntegral_iff
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open PDivisibleGroup Coalgebra
p2m_open_scoped "TensorProduct Coalgebra.TensorProduct"

namespace PDivRootR

variable (p : ℕ) [Fact p.Prime]

section Base

variable (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)]

abbrev O : Subalgebra R (PadicAlgCl p) := integralClosure R (PadicAlgCl p)

abbrev K : Type := PadicAlgCl p

abbrev maxI : Ideal (O p R) := (Ideal.span {(p : O p R)}).radical

abbrev OK : Prop := ∀ x : PadicAlgCl p, IsIntegral R x ↔ ‖x‖ ≤ 1

scoped instance instCommRingO : CommRing (O p R) := inferInstance
scoped instance instAlgebraO : Algebra R (O p R) := inferInstance
scoped instance instModuleO : Module R (O p R) := inferInstance

variable {R}
variable (hO : OK p R)

theorem norm_coe_p : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p]
  exact (PadicAlgCl.norm_extends (p := p) (p : ℚ_[p])).trans (Padic.norm_p (p := p))

include hO in
theorem norm_le_one (c : O p R) : ‖(c : K p)‖ ≤ 1 :=
  (hO (c : PadicAlgCl p)).mp c.2

include hO in
theorem mem_maxI_of_norm_lt_one (c : O p R) (hc : ‖(c : K p)‖ < 1) : c ∈ maxI p R := by
  have hp : (0 : ℝ) < (p : ℝ)⁻¹ := by
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hp hc
  refine Ideal.mem_radical_iff.2 ⟨n, Ideal.mem_span_singleton'.2 ?_⟩
  have hp0 : (p : PadicAlgCl p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set d : K p := (c : K p) ^ n / (p : K p) with hd
  have hdn : ‖d‖ ≤ 1 := by
    rw [hd, norm_div, norm_pow, norm_coe_p, div_le_iff₀ (by positivity), one_mul]
    exact hn.le
  have hdint : IsIntegral R d := (hO d).mpr hdn
  refine ⟨⟨d, hdint⟩, Subtype.ext ?_⟩
  change d * (p : K p) = (c : K p) ^ n
  rw [hd, div_mul_cancel₀ _ hp0]

include hO in

theorem isUnit_of_not_mem_maxI (c : O p R) (hc : c ∉ maxI p R) : IsUnit c := by
  have h1 : ‖(c : K p)‖ = 1 := by
    rcases (norm_le_one p hO c).lt_or_eq with hlt | heq
    · exact absurd (mem_maxI_of_norm_lt_one p hO c hlt) hc
    · exact heq
  have hc0 : (c : K p) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
  have hinv : IsIntegral R (c : K p)⁻¹ := by
    refine (hO _).mpr ?_
    rw [norm_inv, h1, inv_one]
  refine isUnit_iff_exists_inv.2 ⟨⟨(c : K p)⁻¹, hinv⟩, Subtype.ext ?_⟩
  change (c : K p) * (c : K p)⁻¹ = 1
  exact mul_inv_cancel₀ hc0

include hO in

theorem not_isUnit_p : ¬ IsUnit (p : O p R) := by
  intro hu
  obtain ⟨u, hu⟩ := hu
  set v : O p R := ((u⁻¹ : (O p R)ˣ) : O p R) with hv
  have h1 : ‖(v : K p)‖ ≤ 1 := norm_le_one p hO v
  have h2 : ((p : O p R) : K p) * (v : K p) = 1 := by
    rw [← hu, hv, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
  have h3 : ‖((p : O p R) : K p)‖ * ‖(v : K p)‖ = 1 := by
    rw [← norm_mul, h2, norm_one]
  have hp : ‖((p : O p R) : K p)‖ = (p : ℝ)⁻¹ := by
    rw [show ((p : O p R) : K p) = (p : K p) from rfl, norm_coe_p]
  rw [hp] at h3
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have : (p : ℝ)⁻¹ * ‖(v : K p)‖ < 1 := by
    calc (p : ℝ)⁻¹ * ‖(v : K p)‖ ≤ (p : ℝ)⁻¹ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ hp1
  linarith

include hO in
theorem maxI_ne_top : maxI p R ≠ ⊤ := by
  intro htop
  have h1 : (1 : O p R) ∈ maxI p R := by rw [htop]; exact Submodule.mem_top
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 h1
  rw [one_pow, Ideal.mem_span_singleton] at hn
  exact not_isUnit_p p hO (isUnit_of_dvd_one hn)

include hO in

theorem isLocalRing_O : IsLocalRing (O p R) :=
  IsLocalRing.of_nonunits_add (by
    intro a b ha hb hab
    have ha' : a ∈ maxI p R := by
      by_contra h; exact ha (isUnit_of_not_mem_maxI p hO a h)
    have hb' : b ∈ maxI p R := by
      by_contra h; exact hb (isUnit_of_not_mem_maxI p hO b h)
    have habm : a + b ∈ maxI p R := Ideal.add_mem _ ha' hb'

    exact maxI_ne_top p hO (Ideal.eq_top_of_isUnit_mem _ habm hab))

end Base

section Levels

variable {R : Type} [CommRing R] {q h : ℕ} (G : PDivisibleGroup R q h)

def transitionLE {v w : ℕ} (hvw : v ≤ w) : G.level w →ₐ[R] G.level v :=
  Nat.leRec (motive := fun w _ => G.level w →ₐ[R] G.level v) (AlgHom.id R _)
    (fun w _ ih => ih.comp (G.transitionAlgHom w)) hvw

@[scoped simp] theorem transitionLE_self (v : ℕ) : transitionLE G (le_refl v) = AlgHom.id R _ := by
  rw [transitionLE, Nat.leRec_self]

theorem transitionLE_succ {v w : ℕ} (hvw : v ≤ w) :
    transitionLE G (Nat.le_succ_of_le hvw) = (transitionLE G hvw).comp (G.transitionAlgHom w) := by
  rw [transitionLE, Nat.leRec_succ (h1 := hvw)]
  rfl

theorem transitionLE_surjective {v w : ℕ} (hvw : v ≤ w) : Function.Surjective (transitionLE G hvw) := by
  induction hvw with
  | refl => rw [transitionLE_self]; exact Function.surjective_id
  | step hvw ih =>
    rw [transitionLE_succ]
    exact ih.comp (G.transition_surjective _)

theorem toAlgHom_pointInclLE {L : Type} [CommRing L] [Algebra R L] {v w : ℕ} (hvw : v ≤ w)
    (x : G.Point L v) :
    Point.toAlgHom (G.pointInclLE L hvw x) = (Point.toAlgHom x).comp (transitionLE G hvw) := by
  induction hvw with
  | refl => rw [G.pointInclLE_self, transitionLE_self, AlgHom.comp_id]
  | step hvw ih =>
    rw [G.pointInclLE_succ hvw, transitionLE_succ, toAlgHom_pointIncl, ih, AlgHom.comp_assoc]

theorem pointInclLE_apply {L : Type} [CommRing L] [Algebra R L] {v w : ℕ} (hvw : v ≤ w)
    (x : G.Point L v) (a : G.level w) :
    Point.toAlgHom (G.pointInclLE L hvw x) a = Point.toAlgHom x (transitionLE G hvw a) := by
  rw [toAlgHom_pointInclLE]; rfl

theorem nsmulAlgHom_transitionLE {v w : ℕ} (hvw : v ≤ w) (n : ℕ) (a : G.level w) :
    Hopf.nsmulAlgHom R (G.level v) n (transitionLE G hvw a) =
      transitionLE G hvw (Hopf.nsmulAlgHom R (G.level w) n a) := by
  induction hvw with
  | refl => simp
  | step hvw ih =>
    rw [transitionLE_succ, AlgHom.comp_apply, AlgHom.comp_apply, ih]
    change _ = transitionLE G hvw (G.transition _ (Hopf.nsmulAlgHom R _ n a))
    rw [← G.nsmulAlgHom_transition]
    rfl

theorem transition_transitionLE_succ {v w : ℕ} (hvw : v ≤ w) (a : G.level (w + 1)) :
    G.transition v (transitionLE G (Nat.succ_le_succ hvw) a) =
      transitionLE G hvw (G.transition w a) := by
  induction hvw with
  | refl =>
    have h1 : transitionLE G (Nat.succ_le_succ (le_refl v)) = AlgHom.id R _ := transitionLE_self G (v + 1)
    have h2 : transitionLE G (le_refl v) = AlgHom.id R _ := transitionLE_self G v
    rw [h1, h2]; rfl
  | @step w hvw ih =>
    have h1 : transitionLE G (Nat.succ_le_succ (Nat.le.step hvw)) =
        (transitionLE G (Nat.succ_le_succ hvw)).comp (G.transitionAlgHom (w + 1)) :=
      transitionLE_succ G (Nat.succ_le_succ hvw)
    rw [h1, AlgHom.comp_apply, ih, transitionLE_succ, AlgHom.comp_apply]
    rfl

end Levels

section Isog

variable {R : Type} [CommRing R] {h : ℕ} (G : PDivisibleGroup R p h)

abbrev C (w : ℕ) : Subalgebra R (G.level (w + 1)) :=
  (Hopf.nsmulAlgHom R (G.level (w + 1)) p).range

def eC (w : ℕ) : G.level w ≃ₐ[R] ↥(C p G w) :=
  (PDivisibleGroup.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk G w).1.choose

theorem eC_transition (w : ℕ) (a : G.level (w + 1)) :
    ((eC p G w (G.transition w a) : ↥(C p G w)) : G.level (w + 1)) =
      Hopf.nsmulAlgHom R (G.level (w + 1)) p a :=
  (PDivisibleGroup.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk G w).1.choose_spec a

scoped instance finite_overC (w : ℕ) : Module.Finite ↥(C p G w) (G.level (w + 1)) :=
  (PDivisibleGroup.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk G w).2.1

scoped instance projective_overC (w : ℕ) : Module.Projective ↥(C p G w) (G.level (w + 1)) :=
  (PDivisibleGroup.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk G w).2.2.1

theorem rankAtStalk_overC (w : ℕ) (𝔮 : PrimeSpectrum ↥(C p G w)) :
    Module.rankAtStalk (R := ↥(C p G w)) (G.level (w + 1)) 𝔮 = p ^ h :=
  (PDivisibleGroup.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk G w).2.2.2.2 𝔮

theorem exists_eq_eC (w : ℕ) (c : ↥(C p G w)) : ∃ a : G.level (w + 1), c = eC p G w (G.transition w a) := by
  obtain ⟨a, ha⟩ := c.2
  refine ⟨a, Subtype.ext ?_⟩
  rw [eC_transition]
  exact ha.symm

end Isog

section Fib

variable {R : Type} [CommRing R] {h : ℕ} (G : PDivisibleGroup R p h)
variable {S : Type} [CommRing S] [Algebra R S] (w : ℕ) (φ : ↥(C p G w) →ₐ[R] S)

def J : Ideal (S ⊗[R] G.level (w + 1)) :=
  Ideal.span {x | ∃ c : ↥(C p G w), x = φ c ⊗ₜ[R] 1 - 1 ⊗ₜ[R] (c : G.level (w + 1))}

abbrev Fib : Type := (S ⊗[R] G.level (w + 1)) ⧸ J p G w φ

def fibQ : S ⊗[R] G.level (w + 1) →ₐ[S] Fib p G w φ := Ideal.Quotient.mkₐ S (J p G w φ)

theorem fibQ_apply (x : S ⊗[R] G.level (w + 1)) : fibQ p G w φ x = Ideal.Quotient.mk (J p G w φ) x := rfl

theorem fibQ_surjective : Function.Surjective (fibQ p G w φ) := Ideal.Quotient.mk_surjective

def fibMk : G.level (w + 1) →ₐ[R] Fib p G w φ :=
  ((fibQ p G w φ).restrictScalars R).comp Algebra.TensorProduct.includeRight

theorem fibMk_apply (a : G.level (w + 1)) :
    fibMk p G w φ a = fibQ p G w φ (1 ⊗ₜ[R] a) := rfl

theorem algebraMap_fib (s : S) :
    (algebraMap S (Fib p G w φ) : S →+* Fib p G w φ) s = fibQ p G w φ (s ⊗ₜ[R] 1) := rfl

theorem fibQ_one_tmul_coe (c : ↥(C p G w)) :
    fibQ p G w φ (1 ⊗ₜ[R] (c : G.level (w + 1))) = fibQ p G w φ (φ c ⊗ₜ[R] 1) := by
  rw [fibQ_apply, fibQ_apply, eq_comm, Ideal.Quotient.eq]
  exact Ideal.subset_span ⟨c, rfl⟩

theorem fibMk_coe (c : ↥(C p G w)) :
    fibMk p G w φ (c : G.level (w + 1)) = (algebraMap S (Fib p G w φ) : S →+* Fib p G w φ) (φ c) :=
  fibQ_one_tmul_coe p G w φ c

theorem fibQ_one_tmul_nsmulAlgHom (a : G.level (w + 1)) :
    fibQ p G w φ (1 ⊗ₜ[R] Hopf.nsmulAlgHom R (G.level (w + 1)) p a) =
      fibQ p G w φ (φ (eC p G w (G.transition w a)) ⊗ₜ[R] 1) := by
  rw [← fibQ_one_tmul_coe, eC_transition]

theorem fibMk_nsmulAlgHom (a : G.level (w + 1)) :
    fibMk p G w φ (Hopf.nsmulAlgHom R (G.level (w + 1)) p a) =
      (algebraMap S (Fib p G w φ) : S →+* Fib p G w φ) (φ (eC p G w (G.transition w a))) :=
  fibQ_one_tmul_nsmulAlgHom p G w φ a

theorem fibQ_tmul (s : S) (a : G.level (w + 1)) :
    fibQ p G w φ (s ⊗ₜ[R] a) = s • fibMk p G w φ a := by
  rw [fibMk_apply, ← map_smul (fibQ p G w φ), TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem fibQ_tmul_eq_mul (s : S) (a : G.level (w + 1)) :
    fibQ p G w φ (s ⊗ₜ[R] a) =
      (algebraMap S (Fib p G w φ) : S →+* Fib p G w φ) s * fibMk p G w φ a := by
  rw [algebraMap_fib, fibMk_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

scoped instance fib_finite : Module.Finite S (Fib p G w φ) :=
  Module.Finite.of_surjective (fibQ p G w φ).toLinearMap (fibQ_surjective p G w φ)

section Lift

variable {S' : Type} [CommRing S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable (g : G.level (w + 1) →ₐ[R] S') (hg : ∀ c : ↥(C p G w), g c = algebraMap S S' (φ c))

def preLift : S ⊗[R] G.level (w + 1) →ₐ[S] S' :=
  Algebra.TensorProduct.lift (Algebra.ofId S S') g (fun _ _ => Commute.all _ _)

theorem preLift_tmul (s : S) (a : G.level (w + 1)) :
    preLift p G w g (s ⊗ₜ[R] a) = algebraMap S S' s * g a :=
  Algebra.TensorProduct.lift_tmul _ _ _ s a

include hg in
theorem J_le_ker_preLift : J p G w φ ≤ RingHom.ker (preLift p G w g) := by
  rw [J, Ideal.span_le]
  rintro _ ⟨c, rfl⟩
  change preLift p G w g (φ c ⊗ₜ[R] 1 - 1 ⊗ₜ[R] (c : G.level (w + 1))) = 0
  rw [map_sub, preLift_tmul, preLift_tmul, map_one, map_one, mul_one, one_mul, hg c, sub_self]

def fibLift : Fib p G w φ →ₐ[S] S' :=
  Ideal.Quotient.liftₐ (J p G w φ) (preLift p G w g) (fun x hx => J_le_ker_preLift p G w φ g hg hx)

theorem fibLift_fibQ (x : S ⊗[R] G.level (w + 1)) :
    fibLift p G w φ g hg (fibQ p G w φ x) = preLift p G w g x := rfl

theorem fibLift_mk (a : G.level (w + 1)) : fibLift p G w φ g hg (fibMk p G w φ a) = g a := by
  rw [fibMk_apply, fibLift_fibQ, preLift_tmul, map_one, one_mul]

end Lift

theorem fib_algHom_ext {S' : Type} [CommRing S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    {u u' : Fib p G w φ →ₐ[S] S'}
    (huu : ∀ a, u (fibMk p G w φ a) = u' (fibMk p G w φ a)) : u = u' := by
  have h : u.comp (fibQ p G w φ) = u'.comp (fibQ p G w φ) := by
    apply Algebra.TensorProduct.ext'
    intro s a
    rw [AlgHom.comp_apply, AlgHom.comp_apply, fibQ_tmul, map_smul, map_smul, huu]
  refine AlgHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := fibQ_surjective p G w φ x
  exact DFunLike.congr_fun h y

end Fib

section Free

variable {R : Type} [CommRing R] {h : ℕ} (G : PDivisibleGroup R p h)
variable {S : Type} [CommRing S] [Algebra R S] (w : ℕ) (φ : ↥(C p G w) →ₐ[R] S)

theorem smul_eq_mul_tmul (hCS : Algebra ↥(C p G w) S)
    (halg : ∀ c : ↥(C p G w), algebraMap ↥(C p G w) S c = φ c)
    (c : ↥(C p G w)) (x : S ⊗[R] G.level (w + 1)) :
    c • x = (φ c ⊗ₜ[R] (1 : G.level (w + 1))) * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul s a =>
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def, halg]
  | add x y hx hy => rw [smul_add, hx, hy, mul_add]

theorem fib_free_finrank [IsLocalRing S] :
    Module.Free S (Fib p G w φ) ∧ Module.finrank S (Fib p G w φ) = p ^ h := by
  letI hCS : Algebra ↥(C p G w) S := φ.toRingHom.toAlgebra
  have halg : ∀ c : ↥(C p G w), algebraMap ↥(C p G w) S c = φ c := fun c => rfl
  haveI : IsScalarTower R ↥(C p G w) S :=
    IsScalarTower.of_algebraMap_eq (fun r => (φ.commutes r).symm)
  set A := G.level (w + 1) with hA
  let θ : S ⊗[R] A →ₐ[S] S ⊗[↥(C p G w)] A :=
    Algebra.TensorProduct.mapOfCompatibleSMul (↥(C p G w)) R S S A
  have hθsurj : Function.Surjective θ := Algebra.TensorProduct.mapOfCompatibleSMul_surjective _ _ _ _ _
  have hθtmul : ∀ (s : S) (a : A), θ (s ⊗ₜ[R] a) = s ⊗ₜ[↥(C p G w)] a := fun s a => rfl

  have hker : RingHom.ker θ = J p G w φ := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ LinearMap.ker (TensorProduct.mapOfCompatibleSMul (↥(C p G w)) R (↥(C p G w)) S A) := by
        rw [LinearMap.mem_ker]
        exact hx
      rw [TensorProduct.AlgebraTensorModule.ker_mapOfCompatibleSMul] at hx'

      have hsub : (Submodule.span ↥(C p G w)
          {x : S ⊗[R] A | ∃ (c : ↥(C p G w)) (m : S) (n : A),
            (c • m) ⊗ₜ[R] n - m ⊗ₜ[R] (c • n) = x} : Set (S ⊗[R] A)) ⊆ J p G w φ := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨c, m, n, rfl⟩ := hy
          have h1 : (c • m) ⊗ₜ[R] n - m ⊗ₜ[R] (c • n) =
              (m ⊗ₜ[R] n) * (φ c ⊗ₜ[R] 1 - 1 ⊗ₜ[R] (c : A)) := by
            rw [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
              mul_one, Algebra.smul_def, halg, mul_comm (φ c) m, Subalgebra.smul_def, smul_eq_mul, mul_comm (c : A) n]
          rw [h1]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨c, rfl⟩)
        | zero => exact Ideal.zero_mem _
        | add y z _ _ hy hz => exact Ideal.add_mem _ hy hz
        | smul c y _ hy =>
          change c • y ∈ J p G w φ
          rw [smul_eq_mul_tmul p G w φ hCS halg]
          exact Ideal.mul_mem_left _ _ hy
      exact hsub hx'
    · rw [J, Ideal.span_le]
      rintro _ ⟨c, rfl⟩
      change θ (φ c ⊗ₜ[R] 1 - 1 ⊗ₜ[R] (c : A)) = 0
      rw [map_sub, hθtmul, hθtmul, ← halg, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
        sub_eq_zero, Subalgebra.smul_def, smul_eq_mul, mul_one]

  let E : Fib p G w φ ≃ₐ[S] S ⊗[↥(C p G w)] A :=
    (Ideal.quotientEquivAlgOfEq S hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hθsurj)
  haveI : Module.Finite S (S ⊗[↥(C p G w)] A) := inferInstance
  haveI : Module.Projective S (S ⊗[↥(C p G w)] A) := inferInstance
  haveI hfree : Module.Free S (S ⊗[↥(C p G w)] A) := Module.free_of_flat_of_isLocalRing
  refine ⟨Module.Free.of_equiv E.toLinearEquiv.symm, ?_⟩
  rw [E.toLinearEquiv.finrank_eq]
  have h1 : Module.rankAtStalk (R := S) (S ⊗[↥(C p G w)] A) (IsLocalRing.closedPoint S) =
      Module.finrank S (S ⊗[↥(C p G w)] A) := by
    rw [Module.rankAtStalk_eq_finrank_of_free]; rfl
  rw [← h1, Module.rankAtStalk_baseChange, rankAtStalk_overC]

end Free

section Map

variable {R : Type} [CommRing R] {h : ℕ} (G : PDivisibleGroup R p h)
variable {S S' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
variable {w w' : ℕ} (hww : w ≤ w') (φ : ↥(C p G w) →ₐ[R] S) (φ' : ↥(C p G w') →ₐ[R] S')
variable (ζ : S' →ₐ[R] S)

abbrev τ : G.level (w' + 1) →ₐ[R] G.level (w + 1) := transitionLE G (Nat.succ_le_succ hww)

def Cond : Prop :=
  ∀ a' : G.level (w' + 1),
    ζ (φ' (eC p G w' (G.transition w' a'))) = φ (eC p G w (G.transition w (τ p G hww a')))

def preMap : S' ⊗[R] G.level (w' + 1) →ₐ[R] Fib p G w φ :=
  ((fibQ p G w φ).restrictScalars R).comp (Algebra.TensorProduct.map ζ (τ p G hww))

theorem preMap_tmul (s' : S') (a' : G.level (w' + 1)) :
    preMap p G hww φ ζ (s' ⊗ₜ[R] a') = fibQ p G w φ (ζ s' ⊗ₜ[R] τ p G hww a') := by
  change fibQ p G w φ (Algebra.TensorProduct.map ζ (τ p G hww) (s' ⊗ₜ[R] a')) = _
  rw [Algebra.TensorProduct.map_tmul]

variable {φ φ' ζ hww}

theorem J_le_ker_preMap (hc : Cond p G hww φ φ' ζ) : J p G w' φ' ≤ RingHom.ker (preMap p G hww φ ζ) := by
  rw [J, Ideal.span_le]
  rintro _ ⟨c', rfl⟩
  obtain ⟨a', rfl⟩ := exists_eq_eC p G w' c'
  change preMap p G hww φ ζ (φ' (eC p G w' (G.transition w' a')) ⊗ₜ[R] 1 -
    1 ⊗ₜ[R] ((eC p G w' (G.transition w' a') : ↥(C p G w')) : G.level (w' + 1))) = 0
  rw [map_sub, preMap_tmul, preMap_tmul, hc a', eC_transition, sub_eq_zero, map_one, map_one,
    ← nsmulAlgHom_transitionLE, fibQ_one_tmul_nsmulAlgHom]

variable (φ φ' ζ hww)

def fibMap (hc : Cond p G hww φ φ' ζ) : Fib p G w' φ' →ₐ[R] Fib p G w φ :=
  Ideal.Quotient.liftₐ (J p G w' φ') (preMap p G hww φ ζ) (fun x hx => J_le_ker_preMap p G hc hx)

variable (hc : Cond p G hww φ φ' ζ)

theorem fibMap_fibQ (x : S' ⊗[R] G.level (w' + 1)) :
    fibMap p G hww φ φ' ζ hc (fibQ p G w' φ' x) = preMap p G hww φ ζ x := rfl

theorem fibMap_fibQ_tmul (s' : S') (a' : G.level (w' + 1)) :
    fibMap p G hww φ φ' ζ hc (fibQ p G w' φ' (s' ⊗ₜ[R] a')) =
      fibQ p G w φ (ζ s' ⊗ₜ[R] τ p G hww a') := by
  rw [fibMap_fibQ, preMap_tmul]

@[scoped simp] theorem fibMap_mk (a' : G.level (w' + 1)) :
    fibMap p G hww φ φ' ζ hc (fibMk p G w' φ' a') = fibMk p G w φ (τ p G hww a') := by
  rw [fibMk_apply p G w' φ', fibMap_fibQ_tmul, map_one]
  rfl

@[scoped simp] theorem fibMap_algebraMap (s' : S') :
    fibMap p G hww φ φ' ζ hc ((algebraMap S' (Fib p G w' φ') : S' →+* Fib p G w' φ') s') =
      (algebraMap S (Fib p G w φ) : S →+* Fib p G w φ) (ζ s') := by
  rw [algebraMap_fib, fibMap_fibQ_tmul, map_one]
  rfl

theorem fibMap_surjective (hζ : Function.Surjective ζ) :
    Function.Surjective (fibMap p G hww φ φ' ζ hc) := by
  intro y
  obtain ⟨x, rfl⟩ := fibQ_surjective p G w φ y
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
  | tmul s a =>
    obtain ⟨s', rfl⟩ := hζ s
    obtain ⟨a', rfl⟩ := transitionLE_surjective G (Nat.succ_le_succ hww) a
    exact ⟨fibQ p G w' φ' (s' ⊗ₜ[R] a'), fibMap_fibQ_tmul p G hww φ φ' ζ hc s' a'⟩
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add, hx', hy', map_add]⟩

end Map

section LinAlg

theorem injective_of_surjective_of_finrank_eq {S : Type} [CommRing S] [Nontrivial S] {M N : Type}
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [Module.Free S M] [Module.Finite S M] [Module.Free S N] [Module.Finite S N]
    (hMN : Module.finrank S M = Module.finrank S N) (f : M →ₗ[S] N) (hf : Function.Surjective f) :
    Function.Injective f := by
  let bM := Module.Free.chooseBasis S M
  let bN := Module.Free.chooseBasis S N
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex S M) =
      Fintype.card (Module.Free.ChooseBasisIndex S N) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_eq_card_chooseBasisIndex, hMN]
  let e : M ≃ₗ[S] N := bM.equiv bN (Fintype.equivOfCardEq hcard)
  exact OrzechProperty.injective_of_surjective_of_injective e.toLinearMap f e.injective hf

theorem exists_eq_smul_of_map_eq_zero {S S' : Type} [CommRing S] [Nontrivial S] [CommRing S']
    (ζ : S' →+* S) (π : S')
    (hζ : ∀ s', ζ s' = 0 → ∃ t, s' = π * t)
    {M' M : Type} [AddCommGroup M'] [Module S' M'] [AddCommGroup M] [Module S M]
    [Module.Free S M] [Module.Finite S M]
    {ι : Type} [Fintype ι] (β : Module.Basis ι S' M') (hrank : Module.finrank S M = Fintype.card ι)
    (r : M' →+ M) (hr : ∀ (s' : S') (x : M'), r (s' • x) = ζ s' • r x)
    (hrs : Function.Surjective r) (x : M') (hx : r x = 0) : ∃ y : M', x = π • y := by
  classical
  let γ : ι → M := fun k => r (β k)
  let g : (ι → S) →ₗ[S] M := Fintype.linearCombination S γ
  have hg_apply : ∀ v : ι → S, g v = ∑ k, v k • γ k := fun v => Fintype.linearCombination_apply S γ v

  have hrg : ∀ x' : M', r x' = g (fun k => ζ (β.repr x' k)) := by
    intro x'
    conv_lhs => rw [← β.sum_repr x']
    rw [map_sum, hg_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hr]
  have hgs : Function.Surjective g := by
    intro m
    obtain ⟨x', rfl⟩ := hrs m
    exact ⟨_, (hrg x').symm⟩
  haveI : Module.Free S (ι → S) := inferInstance
  haveI : Module.Finite S (ι → S) := inferInstance
  have hgi : Function.Injective g :=
    injective_of_surjective_of_finrank_eq (by rw [Module.finrank_fintype_fun_eq_card, hrank]) g hgs
  have h0 : (fun k => ζ (β.repr x k)) = 0 := hgi (by rw [← hrg, hx, map_zero])
  have hk : ∀ k, ∃ t, β.repr x k = π * t := fun k => hζ _ (congrFun h0 k)
  choose t ht using hk
  refine ⟨∑ k, t k • β k, ?_⟩
  conv_lhs => rw [← β.sum_repr x]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ht k, mul_smul]

end LinAlg

section Tower

variable (R : Type) [CommRing R] (S : Type) [CommRing S] [Algebra R S]

abbrev T (i : ℕ) : Type := S ⧸ Ideal.span {(p : S) ^ i}

abbrev mkq (i : ℕ) : S →ₐ[R] T p S i := Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ i})

theorem mkq_surjective (i : ℕ) : Function.Surjective (mkq p R S i) := Ideal.Quotient.mk_surjective

theorem mkq_eq_zero_iff (i : ℕ) (x : S) : mkq p R S i x = 0 ↔ x ∈ Ideal.span {(p : S) ^ i} :=
  Ideal.Quotient.eq_zero_iff_mem

theorem mkq_pow_eq_zero (i : ℕ) : mkq p R S i ((p : S) ^ i) = 0 :=
  (mkq_eq_zero_iff p R S i _).2 (Ideal.mem_span_singleton_self _)

theorem subsingleton_T_zero : Subsingleton (T p S 0) :=
  Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.span_singleton_one])

variable {S} in
theorem nontrivial_T (hpS : ¬ IsUnit (p : S)) {i : ℕ} (hi : 1 ≤ i) : Nontrivial (T p S i) := by
  refine Ideal.Quotient.nontrivial_iff.2 ?_
  rw [Ne, Ideal.span_singleton_eq_top]
  exact fun hu => hpS (isUnit_of_dvd_unit (dvd_pow_self _ (by omega)) hu)

variable {S} in
theorem isLocalRing_T [IsLocalRing S] (hpS : ¬ IsUnit (p : S)) {i : ℕ} (hi : 1 ≤ i) :
    IsLocalRing (T p S i) :=
  haveI := nontrivial_T p hpS hi
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {(p : S) ^ i})) Ideal.Quotient.mk_surjective

abbrev red (i : ℕ) : T p S (i + 1) →ₐ[R] T p S i := reduceModPow R p S i

theorem red_mkq (i : ℕ) (x : S) : red p R S i (mkq p R S (i + 1) x) = mkq p R S i x := rfl

theorem red_surjective (i : ℕ) : Function.Surjective (red p R S i) := by
  intro y
  obtain ⟨x, rfl⟩ := mkq_surjective p R S i y
  exact ⟨mkq p R S (i + 1) x, rfl⟩

theorem exists_of_red_eq_zero (i : ℕ) (s' : T p S (i + 1)) (hs : red p R S i s' = 0) :
    ∃ t, s' = mkq p R S (i + 1) ((p : S) ^ i) * t := by
  obtain ⟨x, rfl⟩ := mkq_surjective p R S (i + 1) s'
  rw [red_mkq, mkq_eq_zero_iff, Ideal.mem_span_singleton] at hs
  obtain ⟨y, rfl⟩ := hs
  exact ⟨mkq p R S (i + 1) y, by rw [map_mul]⟩

theorem red_pow_eq_zero (i : ℕ) : red p R S i (mkq p R S (i + 1) ((p : S) ^ i)) = 0 := by
  rw [red_mkq, mkq_pow_eq_zero]

variable {h : ℕ} (G : PDivisibleGroup R p h) (X : G.CPoints S)

def lv (i : ℕ) : ℕ := (Points.exists_mkAdd G (G.cpointsProj S i X)).choose

def rep (i : ℕ) : G.Point (T p S i) (lv p R S G X i) :=
  (Points.exists_mkAdd G (G.cpointsProj S i X)).choose_spec.choose

theorem rep_spec (i : ℕ) :
    G.pointsMkAdd (T p S i) (lv p R S G X i) (Additive.ofMul (rep p R S G X i)) = G.cpointsProj S i X :=
  (Points.exists_mkAdd G (G.cpointsProj S i X)).choose_spec.choose_spec

def w (i : ℕ) : ℕ := (Finset.range (i + 1)).sup (lv p R S G X)

theorem lv_le_w (i : ℕ) : lv p R S G X i ≤ w p R S G X i :=
  Finset.le_sup (f := lv p R S G X) (Finset.self_mem_range_succ i)

theorem w_mono {i j : ℕ} (hij : i ≤ j) : w p R S G X i ≤ w p R S G X j :=
  Finset.sup_mono (Finset.range_subset_range.2 (by omega))

theorem hw (i : ℕ) : w p R S G X i ≤ w p R S G X (i + 1) := w_mono p R S G X (Nat.le_succ i)

def f (i : ℕ) : G.Point (T p S i) (w p R S G X i) := G.pointInclLE (T p S i) (lv_le_w p R S G X i) (rep p R S G X i)

theorem f_spec (i : ℕ) :
    G.pointsMkAdd (T p S i) (w p R S G X i) (Additive.ofMul (f p R S G X i)) = G.cpointsProj S i X := by
  rw [f, pointsMkAdd_pointInclLE, rep_spec]

theorem pointMap_red_f (i : ℕ) :
    G.pointMap (red p R S i) (w p R S G X (i + 1)) (f p R S G X (i + 1)) =
      G.pointInclLE (T p S i) (hw p R S G X i) (f p R S G X i) := by
  have hX : G.pointsMap (red p R S i) (G.cpointsProj S (i + 1) X) = G.cpointsProj S i X :=
    CPoints.pointsMap_reduceModPow_succ G S X i
  rw [← f_spec, ← f_spec, pointsMap_pointsMkAdd,
    ← G.pointsMkAdd_pointInclLE (hw p R S G X i) (f p R S G X i), pointsMkAdd_eq_pointsMkAdd_iff] at hX
  exact hX

theorem red_f_apply (i : ℕ) (b : G.level (w p R S G X (i + 1))) :
    red p R S i (Point.toAlgHom (f p R S G X (i + 1)) b) =
      Point.toAlgHom (f p R S G X i) (transitionLE G (hw p R S G X i) b) := by
  have h1 := congrArg Point.toAlgHom (pointMap_red_f p R S G X i)
  rw [toAlgHom_pointMap, toAlgHom_pointInclLE] at h1
  exact DFunLike.congr_fun h1 b

def φ (i : ℕ) : ↥(C p G (w p R S G X i)) →ₐ[R] T p S i :=
  (Point.toAlgHom (f p R S G X i)).comp ((eC p G (w p R S G X i)).symm : ↥(C p G (w p R S G X i)) →ₐ[R] _)

theorem φ_eC (i : ℕ) (b : G.level (w p R S G X i)) :
    φ p R S G X i (eC p G (w p R S G X i) b) = Point.toAlgHom (f p R S G X i) b := by
  change Point.toAlgHom (f p R S G X i) ((eC p G (w p R S G X i)).symm (eC p G (w p R S G X i) b)) = _
  rw [AlgEquiv.symm_apply_apply]

abbrev B (i : ℕ) : Type := Fib p G (w p R S G X i) (φ p R S G X i)

theorem cond_red (i : ℕ) :
    Cond p G (le_refl (w p R S G X (i + 1))) ((red p R S i).comp (φ p R S G X (i + 1))) (φ p R S G X (i + 1))
      (red p R S i) := by
  intro a'
  have h1 : τ p G (le_refl (w p R S G X (i + 1))) a' = a' := by
    change transitionLE G (le_refl _) a' = a'
    rw [transitionLE_self]; rfl
  rw [h1]; rfl

theorem cond_lvl (i : ℕ) :
    Cond p G (hw p R S G X i) (φ p R S G X i) ((red p R S i).comp (φ p R S G X (i + 1))) (AlgHom.id R _) := by
  intro a'
  rw [AlgHom.id_apply, AlgHom.comp_apply, φ_eC, φ_eC, red_f_apply, transition_transitionLE_succ]

def redB (i : ℕ) :
    B p R S G X (i + 1) →ₐ[R] Fib p G (w p R S G X (i + 1)) ((red p R S i).comp (φ p R S G X (i + 1))) :=
  fibMap p G (le_refl _) _ _ (red p R S i) (cond_red p R S G X i)

def lvlB (i : ℕ) :
    Fib p G (w p R S G X (i + 1)) ((red p R S i).comp (φ p R S G X (i + 1))) →ₐ[R] B p R S G X i :=
  fibMap p G (hw p R S G X i) (φ p R S G X i) _ (AlgHom.id R _) (cond_lvl p R S G X i)

def ρ (i : ℕ) : B p R S G X (i + 1) →+* B p R S G X i := ((lvlB p R S G X i).comp (redB p R S G X i)).toRingHom

theorem ρ_apply (i : ℕ) (b : B p R S G X (i + 1)) : ρ p R S G X i b = lvlB p R S G X i (redB p R S G X i b) := rfl

theorem ρ_fibMk (i : ℕ) (a : G.level (w p R S G X (i + 1) + 1)) :
    ρ p R S G X i (fibMk p G _ _ a) = fibMk p G _ _ (τ p G (hw p R S G X i) a) := by
  rw [ρ_apply, redB, fibMap_mk, lvlB, fibMap_mk]
  congr 1
  change τ p G (hw p R S G X i) (transitionLE G (le_refl _) a) = _
  rw [transitionLE_self]; rfl

theorem ρ_algebraMap (i : ℕ) (s : T p S (i + 1)) :
    ρ p R S G X i ((algebraMap (T p S (i + 1)) (B p R S G X (i + 1)) : T p S (i + 1) →+* B p R S G X (i + 1)) s) =
      (algebraMap (T p S i) (B p R S G X i) : T p S i →+* B p R S G X i) (red p R S i s) := by
  rw [ρ_apply, redB, fibMap_algebraMap, lvlB, fibMap_algebraMap, AlgHom.id_apply]

theorem ρ_surjective (i : ℕ) : Function.Surjective (ρ p R S G X i) :=
  (fibMap_surjective p G _ _ _ _ (cond_lvl p R S G X i) Function.surjective_id).comp
    (fibMap_surjective p G _ _ _ _ (cond_red p R S G X i) (red_surjective p R S i))

variable [IsLocalRing S] (hpS : ¬ IsUnit (p : S))

include hpS in
theorem freeB (i : ℕ) : Module.Free (T p S i) (B p R S G X i) := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    haveI := subsingleton_T_zero p S
    exact Module.Free.of_subsingleton' _ _
  · haveI := isLocalRing_T p hpS hi
    exact (fib_free_finrank p G (w p R S G X i) (φ p R S G X i)).1

include hpS in
theorem finrank_B {i : ℕ} (hi : 1 ≤ i) : Module.finrank (T p S i) (B p R S G X i) = p ^ h := by
  haveI := isLocalRing_T p hpS hi
  exact (fib_free_finrank p G (w p R S G X i) (φ p R S G X i)).2

include hpS in
theorem free_finrank_mid {i : ℕ} (hi : 1 ≤ i) :
    Module.Free (T p S i) (Fib p G (w p R S G X (i + 1)) ((red p R S i).comp (φ p R S G X (i + 1)))) ∧
      Module.finrank (T p S i) (Fib p G (w p R S G X (i + 1)) ((red p R S i).comp (φ p R S G X (i + 1)))) = p ^ h := by
  haveI := isLocalRing_T p hpS hi
  exact fib_free_finrank p G _ _

omit [IsLocalRing S] in
theorem lvlB_smul (i : ℕ) (s : T p S i)
    (x : Fib p G (w p R S G X (i + 1)) ((red p R S i).comp (φ p R S G X (i + 1)))) :
    lvlB p R S G X i (s • x) = s • lvlB p R S G X i x := by
  obtain ⟨y, rfl⟩ := fibQ_surjective p G _ _ x
  rw [← map_smul (fibQ p G _ _)]
  induction y using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s₀ a =>
    rw [TensorProduct.smul_tmul', lvlB, fibMap_fibQ_tmul, fibMap_fibQ_tmul, AlgHom.id_apply,
      AlgHom.id_apply, ← map_smul (fibQ p G _ _), TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

omit [IsLocalRing S] in
theorem redB_smul (i : ℕ) (s : T p S (i + 1)) (x : B p R S G X (i + 1)) :
    redB p R S G X i (s • x) = red p R S i s • redB p R S G X i x := by
  obtain ⟨y, rfl⟩ := fibQ_surjective p G _ _ x
  rw [← map_smul (fibQ p G _ _)]
  induction y using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s₀ a =>
    rw [TensorProduct.smul_tmul', redB, fibMap_fibQ_tmul, fibMap_fibQ_tmul, ← map_smul (fibQ p G _ _),
      TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

include hpS in
theorem lvlB_injective {i : ℕ} (hi : 1 ≤ i) : Function.Injective (lvlB p R S G X i) := by
  haveI := nontrivial_T p hpS hi
  obtain ⟨hfree, hrank⟩ := free_finrank_mid p R S G X hpS hi
  haveI := hfree
  haveI := freeB p R S G X hpS i
  let L : Fib p G (w p R S G X (i + 1)) ((red p R S i).comp (φ p R S G X (i + 1))) →ₗ[T p S i] B p R S G X i :=
    { toFun := lvlB p R S G X i
      map_add' := fun x y => map_add _ x y
      map_smul' := fun s x => lvlB_smul p R S G X i s x }
  have hL : Function.Surjective L :=
    fibMap_surjective p G _ _ _ _ (cond_lvl p R S G X i) Function.surjective_id
  exact injective_of_surjective_of_finrank_eq (by rw [hrank, finrank_B p R S G X hpS hi]) L hL

include hpS in
theorem ker_ρ (i : ℕ) :
    RingHom.ker (ρ p R S G X i) =
      Ideal.span {(algebraMap (T p S (i + 1)) (B p R S G X (i + 1)) : T p S (i + 1) →+* B p R S G X (i + 1))
        (mkq p R S (i + 1) ((p : S) ^ i))} := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    have h1 : (algebraMap (T p S (0 + 1)) (B p R S G X (0 + 1)) : T p S (0 + 1) →+* B p R S G X (0 + 1))
        (mkq p R S (0 + 1) ((p : S) ^ 0)) = 1 := by
      rw [pow_zero, map_one, map_one]
    rw [h1, Ideal.span_singleton_one]
    haveI := subsingleton_T_zero p S
    haveI : Subsingleton (B p R S G X 0) := by
      haveI : Subsingleton (T p S 0 ⊗[R] G.level (w p R S G X 0 + 1)) := inferInstance
      exact (fibQ_surjective p G (w p R S G X 0) (φ p R S G X 0)).subsingleton
    exact eq_top_iff.2 fun x _ => Subsingleton.elim _ _
  · apply le_antisymm
    · intro x hx
      have hx0 : redB p R S G X i x = 0 := by
        apply lvlB_injective p R S G X hpS hi
        rw [map_zero]
        exact hx
      haveI := nontrivial_T p hpS hi
      obtain ⟨hfree, hrank⟩ := free_finrank_mid p R S G X hpS hi
      haveI := hfree
      haveI := freeB p R S G X hpS (i + 1)
      haveI : Nontrivial (T p S (i + 1)) := nontrivial_T p hpS (by omega)
      let β := Module.Free.chooseBasis (T p S (i + 1)) (B p R S G X (i + 1))
      have hcard : Module.finrank (T p S i) (Fib p G (w p R S G X (i + 1)) ((red p R S i).comp (φ p R S G X (i + 1)))) =
          Fintype.card (Module.Free.ChooseBasisIndex (T p S (i + 1)) (B p R S G X (i + 1))) := by
        rw [hrank, ← Module.finrank_eq_card_chooseBasisIndex, finrank_B p R S G X hpS (by omega)]
      obtain ⟨y, hy⟩ := exists_eq_smul_of_map_eq_zero (red p R S i : T p S (i + 1) →+* T p S i)
        (mkq p R S (i + 1) ((p : S) ^ i)) (exists_of_red_eq_zero p R S i) β hcard
        (redB p R S G X i).toRingHom.toAddMonoidHom (fun s x => redB_smul p R S G X i s x)
        (fibMap_surjective p G _ _ _ _ (cond_red p R S G X i) (red_surjective p R S i)) x hx0
      rw [hy]
      exact Ideal.mem_span_singleton.2 ⟨y, Algebra.smul_def (mkq p R S (i + 1) ((p : S) ^ i)) y⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, ρ_algebraMap,
        red_pow_eq_zero, map_zero]

end Tower

section Root

variable (R : Type) [CommRing R] (S : Type) [CommRing S] [Algebra R S] {h : ℕ} (G : PDivisibleGroup R p h) (X : G.CPoints S)

abbrev mS : Ideal S := (Ideal.span {(p : S)}).radical

theorem span_pow_one_le_mS : Ideal.span {(p : S) ^ 1} ≤ mS p S := by
  rw [pow_one]; exact Ideal.le_radical

def resid : T p S 1 →ₐ[R] S ⧸ mS p S := Ideal.Quotient.factorₐ R (span_pow_one_le_mS p S)

theorem resid_mkq (x : S) : resid p R S (mkq p R S 1 x) = Ideal.Quotient.mk _ x := rfl

theorem resid_eq_zero_of_isNilpotent {s : T p S 1} (hs : IsNilpotent s) : resid p R S s = 0 := by
  haveI : IsReduced (S ⧸ mS p S) :=
    (Ideal.isRadical_iff_quotient_reduced _).1 (Ideal.radical_isRadical _)
  exact (hs.map (resid p R S)).eq_zero

theorem counit_transitionLE {v u : ℕ} (hvu : v ≤ u) (a : G.level u) :
    counit (R := R) (transitionLE G hvu a) = counit (R := R) a := by
  induction hvu with
  | refl => rw [transitionLE_self]; rfl
  | @step u hvu ih =>
    rw [transitionLE_succ G hvu, AlgHom.comp_apply, ih]
    exact G.counit_transition _ a

def gε (v : ℕ) : G.level v →ₐ[R] S ⧸ mS p S :=
  ((Ideal.Quotient.mkₐ R (mS p S)).comp (Algebra.ofId R S)).comp (Bialgebra.counitAlgHom R (G.level v))

theorem gε_apply (v : ℕ) (a : G.level v) :
    gε p R S G v a = algebraMap R (S ⧸ mS p S) (counit (R := R) a) := rfl

variable (hX : ∀ (v : ℕ) (g : G.Point (T p S 1) v),
  G.pointsMkAdd (T p S 1) v (Additive.ofMul g) = G.cpointsProj S 1 X →
    ∀ a : G.level v, IsNilpotent (Point.toAlgHom g a - algebraMap R (T p S 1) (counit (R := R) a)))

include hX in

theorem resid_f_one (b : G.level (w p R S G X 1)) :
    resid p R S (Point.toAlgHom (f p R S G X 1) b) = algebraMap R (S ⧸ mS p S) (counit (R := R) b) := by
  have hn := hX (w p R S G X 1) (f p R S G X 1) (f_spec p R S G X 1) b
  have h0 := resid_eq_zero_of_isNilpotent p R S hn
  rw [map_sub, sub_eq_zero, AlgHom.commutes] at h0
  exact h0

include hX in
theorem gε_coe (c : ↥(C p G (w p R S G X 1))) :
    gε p R S G (w p R S G X 1 + 1) c = resid p R S (φ p R S G X 1 c) := by
  obtain ⟨a', rfl⟩ := exists_eq_eC p G (w p R S G X 1) c
  rw [φ_eC, resid_f_one p R S G X hX, gε_apply, eC_transition, Hopf.counit_nsmulAlgHom, G.counit_transition]

def ψ (hX' : ∀ c : ↥(C p G (w p R S G X 1)), gε p R S G (w p R S G X 1 + 1) c = resid p R S (φ p R S G X 1 c)) :
    B p R S G X 1 →+* S ⧸ mS p S := by
  letI : Algebra (T p S 1) (S ⧸ mS p S) := (resid p R S).toRingHom.toAlgebra
  haveI : IsScalarTower R (T p S 1) (S ⧸ mS p S) :=
    IsScalarTower.of_algebraMap_eq (fun r => ((resid p R S).commutes r).symm)
  exact (fibLift p G (w p R S G X 1) (φ p R S G X 1) (gε p R S G (w p R S G X 1 + 1)) (fun c => hX' c)).toRingHom

theorem ψ_fibMk (hX') (a : G.level (w p R S G X 1 + 1)) :
    ψ p R S G X hX' (fibMk p G _ _ a) = gε p R S G _ a := by
  letI : Algebra (T p S 1) (S ⧸ mS p S) := (resid p R S).toRingHom.toAlgebra
  haveI : IsScalarTower R (T p S 1) (S ⧸ mS p S) :=
    IsScalarTower.of_algebraMap_eq (fun r => ((resid p R S).commutes r).symm)
  exact fibLift_mk p G (w p R S G X 1) (φ p R S G X 1) (gε p R S G (w p R S G X 1 + 1)) (fun c => hX' c) a

theorem ψ_algebraMap (hX') (s : T p S 1) :
    ψ p R S G X hX' ((algebraMap (T p S 1) (B p R S G X 1) : T p S 1 →+* B p R S G X 1) s) = resid p R S s := by
  letI : Algebra (T p S 1) (S ⧸ mS p S) := (resid p R S).toRingHom.toAlgebra
  haveI : IsScalarTower R (T p S 1) (S ⧸ mS p S) :=
    IsScalarTower.of_algebraMap_eq (fun r => ((resid p R S).commutes r).symm)
  exact (fibLift p G (w p R S G X 1) (φ p R S G X 1) (gε p R S G (w p R S G X 1 + 1)) (fun c => hX' c)).commutes s

variable [IsLocalRing S] (hpS : ¬ IsUnit (p : S))

def SectionsHyp : Prop :=
  ∀ (Bt : ℕ → Type) [∀ i, CommRing (Bt i)] [∀ i, Algebra (T p S i) (Bt i)]
    [∀ i, Module.Finite (T p S i) (Bt i)] [∀ i, Module.Free (T p S i) (Bt i)]
    (ρt : ∀ i, Bt (i + 1) →+* Bt i)
    (_hρ : ∀ (i : ℕ) (x : S),
      ρt i (algebraMap (T p S (i + 1)) (Bt (i + 1)) (Ideal.Quotient.mk _ x)) =
        algebraMap (T p S i) (Bt i) (Ideal.Quotient.mk _ x))
    (_hρs : ∀ i, Function.Surjective (ρt i))
    (_hker : ∀ i, RingHom.ker (ρt i) =
      Ideal.span {algebraMap (T p S (i + 1)) (Bt (i + 1)) (Ideal.Quotient.mk _ ((p : S) ^ i))})
    (ψt : Bt 1 →+* S ⧸ (Ideal.span {(p : S)}).radical)
    (_hψ : ∀ x : S, ψt (algebraMap (T p S 1) (Bt 1) (Ideal.Quotient.mk _ x)) = Ideal.Quotient.mk _ x),
    ∃ σ : ∀ i, Bt i →+* T p S i,
      (∀ (i : ℕ) (x : T p S i), σ i (algebraMap (T p S i) (Bt i) x) = x) ∧
      (∀ (i : ℕ) (b : Bt (i + 1)) (x : S),
        σ (i + 1) b = Ideal.Quotient.mk _ x → σ i (ρt i b) = Ideal.Quotient.mk _ x) ∧
      ∀ b : Bt 1, ψt b = 0 → IsNilpotent (σ 1 b)

include hX hpS in

theorem exists_root (hsec : SectionsHyp p S) :
    ∃ X' : G.CPoints S,
      (∀ (v : ℕ) (g : G.Point (T p S 1) v),
        G.pointsMkAdd (T p S 1) v (Additive.ofMul g) = G.cpointsProj S 1 X' →
          ∀ a : G.level v,
            IsNilpotent (Point.toAlgHom g a - algebraMap R (T p S 1) (counit (R := R) a))) ∧
      p • X' = X := by
  have hX' := gε_coe p R S G X hX

  haveI I4 : ∀ i, Module.Free (T p S i) (B p R S G X i) := fun i => freeB p R S G X hpS i
  have hρ' : ∀ (i : ℕ) (x : S),
      ρ p R S G X i (algebraMap (T p S (i + 1)) (B p R S G X (i + 1)) (Ideal.Quotient.mk _ x)) =
        algebraMap (T p S i) (B p R S G X i) (Ideal.Quotient.mk _ x) :=
    fun i x => ρ_algebraMap p R S G X i (mkq p R S (i + 1) x)
  have hker' : ∀ i, RingHom.ker (ρ p R S G X i) =
      Ideal.span {algebraMap (T p S (i + 1)) (B p R S G X (i + 1)) (Ideal.Quotient.mk _ ((p : S) ^ i))} :=
    fun i => ker_ρ p R S G X hpS i
  have hψ' : ∀ x : S, ψ p R S G X hX' (algebraMap (T p S 1) (B p R S G X 1) (Ideal.Quotient.mk _ x)) =
      Ideal.Quotient.mk _ x :=
    fun x => ψ_algebraMap p R S G X hX' (mkq p R S 1 x)
  have step1 := @hsec (B p R S G X) (fun i => inferInstance) (fun i => inferInstance) (fun i => inferInstance) I4
  have step2 := step1 (ρ p R S G X)
  have step3 := step2 hρ'
  have step4 := step3 (ρ_surjective p R S G X) hker'
  have step5 := step4 (ψ p R S G X hX')
  obtain ⟨σ, hσ1, hσ2, hσ3⟩ := step5 hψ'
  clear step1 step2 step3 step4 step5

  let σA : ∀ i, G.level (w p R S G X i + 1) →ₐ[R] T p S i := fun i =>
    { toRingHom := (σ i).comp (fibMk p G (w p R S G X i) (φ p R S G X i)).toRingHom
      commutes' := fun r => by
        change σ i (fibMk p G _ _ (algebraMap R _ r)) = _
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R (T p S i) (B p R S G X i)]
        exact hσ1 i _ }
  have σA_apply : ∀ i a, σA i a = σ i (fibMk p G _ _ a) := fun i a => rfl
  let gpt : ∀ i, G.Point (T p S i) (w p R S G X i + 1) := fun i => Point.ofAlgHom (σA i)
  have gpt_apply : ∀ i a, Point.toAlgHom (gpt i) a = σ i (fibMk p G _ _ a) := fun i a => rfl

  have hroot : ∀ i, gpt i ^ p = G.pointIncl (T p S i) (w p R S G X i) (f p R S G X i) := by
    intro i
    refine Point.ext fun a => ?_
    rw [Point.toAlgHom_pow, AlgHom.comp_apply, gpt_apply, fibMk_nsmulAlgHom, hσ1, φ_eC, pointIncl_apply]

  have hcompat : ∀ i, G.pointMap (red p R S i) (w p R S G X (i + 1) + 1) (gpt (i + 1)) =
      G.pointInclLE (T p S i) (Nat.succ_le_succ (hw p R S G X i)) (gpt i) := by
    intro i
    refine Point.ext fun a => ?_
    rw [toAlgHom_pointMap, AlgHom.comp_apply, gpt_apply, pointInclLE_apply, gpt_apply]
    obtain ⟨x, hx⟩ := mkq_surjective p R S (i + 1) (σ (i + 1) (fibMk p G _ _ a))
    have h2 := hσ2 i (fibMk p G _ _ a) x hx.symm
    rw [ρ_fibMk] at h2
    change red p R S i (σ (i + 1) (fibMk p G _ _ a)) = σ i (fibMk p G _ _ (τ p G (hw p R S G X i) a))
    rw [h2, ← hx]
    rfl

  let X'fun : ∀ i, G.Points (T p S i) := fun i => G.pointsMkAdd (T p S i) (w p R S G X i + 1) (Additive.ofMul (gpt i))
  have hmem : X'fun ∈ G.CPoints S := by
    intro i
    change G.pointsMap (red p R S i) (G.pointsMkAdd _ _ (Additive.ofMul (gpt (i + 1)))) =
      G.pointsMkAdd _ _ (Additive.ofMul (gpt i))
    rw [pointsMap_pointsMkAdd, hcompat, pointsMkAdd_pointInclLE]
  refine ⟨⟨X'fun, hmem⟩, ?_, ?_⟩
  ·
    intro v g hg a
    have hproj : G.cpointsProj S 1 ⟨X'fun, hmem⟩ = G.pointsMkAdd _ _ (Additive.ofMul (gpt 1)) := rfl
    rw [hproj] at hg

    set m := max v (w p R S G X 1 + 1) with hm
    have h1 : G.pointInclLE (T p S 1) (le_max_left v (w p R S G X 1 + 1)) g =
        G.pointInclLE (T p S 1) (le_max_right v (w p R S G X 1 + 1)) (gpt 1) := by
      rw [← pointsMkAdd_eq_pointsMkAdd_iff, pointsMkAdd_pointInclLE, pointsMkAdd_pointInclLE]
      exact hg
    obtain ⟨b, rfl⟩ := transitionLE_surjective G (le_max_left v (w p R S G X 1 + 1)) a
    have h2 := DFunLike.congr_fun (congrArg Point.toAlgHom h1) b
    rw [pointInclLE_apply, pointInclLE_apply, gpt_apply] at h2
    rw [h2, counit_transitionLE, ← counit_transitionLE p R G (le_max_right v (w p R S G X 1 + 1)) b]
    set b' := transitionLE G (le_max_right v (w p R S G X 1 + 1)) b
    have h3 : σ 1 (fibMk p G _ _ b') - algebraMap R (T p S 1) (counit (R := R) b') =
        σ 1 (fibMk p G _ _ b' - (algebraMap R (B p R S G X 1) : R →+* B p R S G X 1) (counit (R := R) b')) := by
      rw [map_sub, IsScalarTower.algebraMap_apply R (T p S 1) (B p R S G X 1), hσ1]
    rw [h3]
    apply hσ3
    rw [map_sub, ψ_fibMk, sub_eq_zero, gε_apply, IsScalarTower.algebraMap_apply R (T p S 1) (B p R S G X 1),
      ψ_algebraMap, AlgHom.commutes]
  ·
    apply cpointsProj_ext
    intro i
    change p • G.pointsMkAdd _ _ (Additive.ofMul (gpt i)) = G.cpointsProj S i X
    rw [← map_nsmul, ← ofMul_pow, hroot, pointsMkAdd_pointIncl, f_spec]

end Root

section Transport

variable {S S' : Type} [CommRing S] [CommRing S'] (e : S ≃+* S')

def eT (i : ℕ) : T p S i ≃+* T p S' i :=
  Ideal.quotientEquiv (Ideal.span {(p : S) ^ i}) (Ideal.span {(p : S') ^ i}) e (by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {((p : S') ^ i)} = Ideal.span {e ((p : S) ^ i)}
    rw [map_pow, map_natCast])

theorem eT_mk (i : ℕ) (x : S) : eT p e i (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (e x) :=
  Ideal.quotientEquiv_mk _ _ _ _ x

theorem eT_symm_mk (i : ℕ) (x' : S') : (eT p e i).symm (Ideal.Quotient.mk _ x') = Ideal.Quotient.mk _ (e.symm x') := by
  apply (eT p e i).injective
  rw [RingEquiv.apply_symm_apply, eT_mk, RingEquiv.apply_symm_apply]

def eRad : S' ⧸ (Ideal.span {(p : S')}).radical →+* S ⧸ (Ideal.span {(p : S)}).radical :=
  Ideal.quotientMap (Ideal.span {(p : S)}).radical e.symm.toRingHom (by
    intro y hy
    rw [Ideal.mem_comap]
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 hy
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hn
    refine Ideal.mem_radical_iff.2 ⟨n, Ideal.mem_span_singleton'.2 ⟨e.symm z, ?_⟩⟩
    change e.symm z * (p : S) = (e.symm.toRingHom y) ^ n
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ← map_pow, ← hz, map_mul, map_natCast])

theorem eRad_mk (y : S') : eRad p e (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (e.symm y) :=
  Ideal.quotientMap_mk

include e in

theorem sectionsHyp_of_ringEquiv (hS : SectionsHyp p S) : SectionsHyp p S' := by
  intro Bt _ _ _ _ ρt hρ hρs hker ψt hψ

  letI algZ : ∀ i, Algebra (T p S i) (Bt i) := fun i =>
    ((algebraMap (T p S' i) (Bt i)).comp (eT p e i).toRingHom).toAlgebra
  have algZ_def : ∀ (i : ℕ) (z : T p S i), algebraMap (T p S i) (Bt i) z = algebraMap (T p S' i) (Bt i) (eT p e i z) :=
    fun i z => rfl

  have finZ : ∀ i, Module.Finite (T p S i) (Bt i) := by
    intro i
    letI : Algebra (T p S i) (T p S' i) := (eT p e i).toRingHom.toAlgebra
    haveI : IsScalarTower (T p S i) (T p S' i) (Bt i) := IsScalarTower.of_algebraMap_eq (fun z => rfl)
    haveI : Module.Finite (T p S i) (T p S' i) :=
      Module.Finite.of_surjective (Algebra.linearMap (T p S i) (T p S' i)) (eT p e i).surjective
    exact Module.Finite.trans (T p S' i) (Bt i)

  have freeZ : ∀ i, Module.Free (T p S i) (Bt i) := by
    intro i
    refine Module.Free.of_basis ((Module.Free.chooseBasis (T p S' i) (Bt i)).mapCoeffs (eT p e i).symm ?_)
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, algZ_def, RingEquiv.apply_symm_apply]

  have hρZ : ∀ (i : ℕ) (x : S),
      ρt i (algebraMap (T p S (i + 1)) (Bt (i + 1)) (Ideal.Quotient.mk _ x)) =
        algebraMap (T p S i) (Bt i) (Ideal.Quotient.mk _ x) := by
    intro i x
    rw [algZ_def, algZ_def, eT_mk, eT_mk]
    exact hρ i (e x)
  have hkerZ : ∀ i, RingHom.ker (ρt i) =
      Ideal.span {algebraMap (T p S (i + 1)) (Bt (i + 1)) (Ideal.Quotient.mk _ ((p : S) ^ i))} := by
    intro i
    rw [hker i, algZ_def, eT_mk, map_pow e, map_natCast e]
  let ψZ : Bt 1 →+* S ⧸ (Ideal.span {(p : S)}).radical := (eRad p e).comp ψt
  have hψZ : ∀ x : S, ψZ (algebraMap (T p S 1) (Bt 1) (Ideal.Quotient.mk _ x)) = Ideal.Quotient.mk _ x := by
    intro x
    change eRad p e (ψt _) = _
    rw [algZ_def, eT_mk, hψ, eRad_mk, RingEquiv.symm_apply_apply]
  obtain ⟨σ, hσ1, hσ2, hσ3⟩ := @hS Bt _ algZ finZ freeZ ρt hρZ hρs hkerZ ψZ hψZ
  refine ⟨fun i => (eT p e i).toRingHom.comp (σ i), ?_, ?_, ?_⟩
  · intro i y
    change eT p e i (σ i (algebraMap (T p S' i) (Bt i) y)) = y
    have h1 : algebraMap (T p S' i) (Bt i) y = algebraMap (T p S i) (Bt i) ((eT p e i).symm y) := by
      rw [algZ_def, RingEquiv.apply_symm_apply]
    rw [h1, hσ1, RingEquiv.apply_symm_apply]
  · intro i b x' hb
    change eT p e (i + 1) (σ (i + 1) b) = _ at hb
    change eT p e i (σ i (ρt i b)) = _
    have hb' : σ (i + 1) b = Ideal.Quotient.mk _ (e.symm x') := by
      rw [← eT_symm_mk p e, ← hb, RingEquiv.symm_apply_apply]
    rw [hσ2 i b (e.symm x') hb', eT_mk, RingEquiv.apply_symm_apply]
  · intro b hb
    change IsNilpotent (eT p e 1 (σ 1 b))
    refine (hσ3 b ?_).map _
    change eRad p e (ψt b) = 0
    rw [hb, map_zero]

end Transport

section Spec

variable {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)] (hO : OK p R)

abbrev OZ : Subalgebra ℤ_[p] (PadicAlgCl p) := integralClosure ℤ_[p] (PadicAlgCl p)

include hO in
theorem mem_O_iff_mem_OZ (x : PadicAlgCl p) : x ∈ O p R ↔ x ∈ OZ p := by
  change IsIntegral R x ↔ IsIntegral ℤ_[p] x
  rw [hO x, PadicAlgCl.isIntegral_padicInt_iff_norm_le_one]

def eOZ : OZ p ≃+* O p R where
  toFun x := ⟨x.1, (mem_O_iff_mem_OZ p hO x.1).2 x.2⟩
  invFun y := ⟨y.1, (mem_O_iff_mem_OZ p hO y.1).1 y.2⟩
  left_inv x := Subtype.ext rfl
  right_inv y := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl

theorem sectionsHyp_OZ : SectionsHyp p (OZ p) :=
  @fun Bt i1 i2 i3 i4 ρt hρ hρs hker ψt hψ =>
    @PadicAlgCl.exists_forall_ringHom_apply_algebraMap_eq_of_free_of_ker_eq_span_pow p _ Bt i1 i2 i3 i4 ρt hρ
      hρs hker ψt hψ

include hO in

theorem sectionsHyp_O : SectionsHyp p (O p R) :=
  sectionsHyp_of_ringEquiv p (eOZ p hO) (sectionsHyp_OZ p)

end Spec

end PDivRootR
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_nsmul_eq_of_forall_isNilpotent_cpointsProj_one_of_isIntegral_iff.PDivRootR"

end
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_nsmul_eq_of_forall_isNilpotent_cpointsProj_one_of_isIntegral_iff.PDivRootR"

open PDivisibleGroup in

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [Algebra R (PadicAlgCl p)]
    (hO : ∀ x : PadicAlgCl p, IsIntegral R x ↔ ‖x‖ ≤ 1)
    {h : ℕ} (G : PDivisibleGroup R p h)
    (X : G.CPoints (integralClosure R (PadicAlgCl p)))
    (hX : ∀ (w : ℕ) (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
        Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ 1}) w),
      G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (integralClosure R (PadicAlgCl p)) 1 X →
      ∀ a : G.level w,
        IsNilpotent (PDivisibleGroup.Point.toAlgHom f a - algebraMap R _ (Coalgebra.counit a))) :
    ∃ X' : G.CPoints (integralClosure R (PadicAlgCl p)),
      (∀ (w : ℕ) (f : G.Point (integralClosure R (PadicAlgCl p) ⧸
          Ideal.span {(p : integralClosure R (PadicAlgCl p)) ^ 1}) w),
        G.pointsMkAdd _ w (Additive.ofMul f) = G.cpointsProj (integralClosure R (PadicAlgCl p)) 1 X' →
        ∀ a : G.level w,
          IsNilpotent (PDivisibleGroup.Point.toAlgHom f a - algebraMap R _ (Coalgebra.counit a))) ∧
      p • X' = X :=
  haveI := PDivRootR.isLocalRing_O p hO
  PDivRootR.exists_root p R (PDivRootR.O p R) G X hX (PDivRootR.not_isUnit_p p hO) (PDivRootR.sectionsHyp_O p hO)

end S_PDivisibleGroup_exists_nsmul_eq_of_forall_isNilpotent_cpointsProj_one_of_isIntegral_iff
end P2MW
export P2MW.S_PDivisibleGroup_exists_nsmul_eq_of_forall_isNilpotent_cpointsProj_one_of_isIntegral_iff (solution)
