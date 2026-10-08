-- Prove2me | solution 1 for ProximityUniversalReplacementV1.no_strict_universal_replacement
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-04T14:25:26.173209+00:00
-- url     : https://prove2.me/submissions/0978037f-ae03-4fd0-8e9b-7063878db5ac

import Definitions.Def_ProximityUniversalReplacementV1
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace ProximityUniversalReplacementV1
open scoped BigOperators
open MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def weightEmbed (weights:Fin 4 → ℕ):(Fin 4 →₀ ℕ) →+(Fin 5 →₀ ℕ) where
 toFun d:=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+
   Finsupp.single 2 (d 2)+Finsupp.single 3 (d 3)+
   Finsupp.single 4 (Finsupp.weight weights d)
 map_zero':=by simp
 map_add' d e:=by
   ext i
   fin_cases i <;> simp [Finsupp.add_apply,map_add]
theorem weightEmbed_castSucc (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ) (i:Fin 4):
   weightEmbed weights d i.castSucc=d i:=by
 fin_cases i <;> simp [weightEmbed]
theorem weightEmbed_last (weights:Fin 4 → ℕ) (d:Fin 4 →₀ ℕ):
   weightEmbed weights d (4:Fin 5)=Finsupp.weight weights d:=by
 simp [weightEmbed]
theorem weightEmbed_injective (weights:Fin 4 → ℕ):
   Function.Injective (weightEmbed weights):=by
 intro d e h
 ext i
 have hi:=congrArg (fun a:Fin 5 →₀ ℕ => a i.castSucc) h
 simpa only [weightEmbed_castSucc] using hi
variable {K:Type*} [Field K]
def weightedLift (K:Type*) [Field K] (weights:Fin 4 → ℕ):
   MvPolynomial (Fin 4) K →+*MvPolynomial (Fin 5) K:=
 AddMonoidAlgebra.mapDomainRingHom K (weightEmbed weights)
theorem weightedLift_injective (weights:Fin 4 → ℕ):
   Function.Injective (weightedLift K weights):=
 AddMonoidAlgebra.mapDomain_injective (weightEmbed_injective weights)
theorem weightedLift_ne_zero (weights:Fin 4 → ℕ) (P:MvPolynomial (Fin 4) K)
   (hP:P≠0):weightedLift K weights P≠0:=by
 intro hzero
 apply hP
 apply weightedLift_injective weights
 simpa only [map_zero] using hzero
theorem support_weightedLift (weights:Fin 4 → ℕ) (P:MvPolynomial (Fin 4) K):
   (weightedLift K weights P).support=P.support.image (weightEmbed weights):=by
 change (Finsupp.mapDomain (weightEmbed weights) (AddMonoidAlgebra.coeff P)).support=
   Finset.image (weightEmbed weights) (AddMonoidAlgebra.coeff P).support
 exact Finsupp.mapDomain_support_of_injective (weightEmbed_injective weights) _
theorem degree_weightedLift (weights:Fin 4 → ℕ) (P:MvPolynomial (Fin 4) K):
   (weightedLift K weights P).degreeOf (4:Fin 5)=
     MvPolynomial.weightedTotalDegree weights P:=by
 change (weightedLift K weights P).degreeOf (4:Fin 5)=
   P.support.sup (Finsupp.weight weights)
 rw [MvPolynomial.degreeOf_eq_sup,support_weightedLift,Finset.sup_image]
 apply congrArg (fun f:(Fin 4 →₀ ℕ) → ℕ => P.support.sup f)
 funext d
 exact weightEmbed_last weights d
theorem weightedTotalDegree_mul (weights:Fin 4 → ℕ)
   (P Q:MvPolynomial (Fin 4) K) (hP:P≠0) (hQ:Q≠0):
   MvPolynomial.weightedTotalDegree weights (P*Q)=
     MvPolynomial.weightedTotalDegree weights P+
       MvPolynomial.weightedTotalDegree weights Q:=by
 calc
   MvPolynomial.weightedTotalDegree weights (P*Q)=
       (weightedLift K weights (P*Q)).degreeOf (4:Fin 5):=
     (degree_weightedLift weights (P*Q)).symm
   _=(weightedLift K weights P*weightedLift K weights Q).degreeOf (4:Fin 5):=by
     rw [map_mul]
   _=(weightedLift K weights P).degreeOf (4:Fin 5)+
       (weightedLift K weights Q).degreeOf (4:Fin 5):=
     MvPolynomial.degreeOf_mul_eq (weightedLift_ne_zero weights P hP)
       (weightedLift_ne_zero weights Q hQ)
   _=MvPolynomial.weightedTotalDegree weights P+
       MvPolynomial.weightedTotalDegree weights Q:=by
     rw [degree_weightedLift,degree_weightedLift]

variable {I : Type*}

theorem eval_one_weightedPolynomial (weights : Fin 4 → ℕ) (P : Poly4 K) :
    Polynomial.eval 1 (weightedPolynomial K weights P) = P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [weightedPolynomial]
  | add P Q hP hQ => simp only [map_add, Polynomial.eval_add, hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, Polynomial.eval_mul, hP]
      simp [weightedPolynomial]

theorem weightedPolynomial_ne_zero (weights : Fin 4 → ℕ) {P : Poly4 K} (hP : P ≠ 0) :
    weightedPolynomial K weights P ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval (1 : Poly4 K)) h
  rw [eval_one_weightedPolynomial] at he
  exact hP (by simpa using he)

def delocalize (x u0 u1 : K) : Poly4 K →ₐ[K] Poly4 K :=
  MvPolynomial.aeval ![MvPolynomial.X 0 - MvPolynomial.C x,
    MvPolynomial.X 1 - MvPolynomial.C u0 - MvPolynomial.X 3 * MvPolynomial.C u1 -
      MvPolynomial.X 2 * (MvPolynomial.X 0 - MvPolynomial.C x),
    MvPolynomial.X 2, MvPolynomial.X 3]

theorem delocalize_localize (x u0 u1 : K) (P : Poly4 K) :
    delocalize x u0 u1 (localize K x u0 u1 P) = P := by
  have he : (delocalize x u0 u1).comp (localize K x u0 u1) =
      AlgHom.id K (Poly4 K) := by
    ext i
    fin_cases i <;> simp [delocalize, localize]
  exact DFunLike.congr_fun he P

theorem contactPolynomial_ne_zero (x u0 u1 : K) {P : Poly4 K} (hP : P ≠ 0) :
    contactPolynomial K x u0 u1 P ≠ 0 := by
  change weightedPolynomial K ![1, 2, 0, 0] (localize K x u0 u1 P) ≠ 0
  apply weightedPolynomial_ne_zero
  intro h
  have he := congrArg (delocalize x u0 u1) h
  rw [delocalize_localize, map_zero] at he
  exact hP he

theorem contactAtLeast_iff_le (x u0 u1 : K) (m : ℕ) (P : Poly4 K) (hP : P ≠ 0) :
    contactAtLeast K x u0 u1 m P ↔ m ≤ contactOrder K x u0 u1 P := by
  rw [contactAtLeast, Polynomial.X_pow_dvd_iff]
  constructor
  · intro h
    by_contra hm
    have hz := h (contactOrder K x u0 u1 P) (by omega)
    exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr
      (contactPolynomial_ne_zero x u0 u1 hP)) hz
  · intro h n hn
    apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
    exact lt_of_lt_of_le hn h

theorem contactOrder_mul (x u0 u1 : K) (P Q : Poly4 K) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    contactOrder K x u0 u1 (P * Q) =
      contactOrder K x u0 u1 P + contactOrder K x u0 u1 Q := by
  unfold contactOrder
  rw [map_mul, Polynomial.natTrailingDegree_mul
    (contactPolynomial_ne_zero x u0 u1 hP)
    (contactPolynomial_ne_zero x u0 u1 hQ)]

end
end ProximityUniversalReplacementV1

namespace ProximityUniversalReplacementV1
open MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

def frontEmbed (weights : Fin 4 → ℕ) : (Fin 4 →₀ ℕ) →+ (Fin 5 →₀ ℕ) where
  toFun d := d.cons (Finsupp.weight weights d)
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' d e := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [map_add]

theorem frontEmbed_injective (weights : Fin 4 → ℕ) :
    Function.Injective (frontEmbed weights) := by
  intro d e h
  have he := congrArg Finsupp.tail h
  simpa [frontEmbed] using he

def frontLift (K : Type*) [Field K] (weights : Fin 4 → ℕ) :
    Poly4 K →+* MvPolynomial (Fin 5) K :=
  AddMonoidAlgebra.mapDomainRingHom K (frontEmbed weights)

theorem support_frontLift (weights : Fin 4 → ℕ) (P : Poly4 K) :
    (frontLift K weights P).support = P.support.image (frontEmbed weights) := by
  change (Finsupp.mapDomain (frontEmbed weights) (AddMonoidAlgebra.coeff P)).support =
    Finset.image (frontEmbed weights) (AddMonoidAlgebra.coeff P).support
  exact Finsupp.mapDomain_support_of_injective (frontEmbed_injective weights) _

theorem frontEmbed_single (weights : Fin 4 → ℕ) (i : Fin 4) :
    frontEmbed weights (Finsupp.single i 1) =
      Finsupp.single 0 (weights i) + Finsupp.single i.succ 1 := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [frontEmbed, Finsupp.weight_single]
  · simp [frontEmbed, Finsupp.weight_single, Finsupp.single_apply]

theorem frontLift_C (weights : Fin 4 → ℕ) (a : K) :
    frontLift K weights (C a) = C a := by
  change AddMonoidAlgebra.mapDomainRingHom K (frontEmbed weights)
    (AddMonoidAlgebra.single 0 a) = AddMonoidAlgebra.single 0 a
  simp

theorem frontLift_X (weights : Fin 4 → ℕ) (i : Fin 4) :
    frontLift K weights (X i) = X (0 : Fin 5) ^ weights i * X i.succ := by
  change AddMonoidAlgebra.mapDomainRingHom K (frontEmbed weights)
    (AddMonoidAlgebra.single (Finsupp.single i 1) 1) = _
  change AddMonoidAlgebra.mapDomain (frontEmbed weights)
    (AddMonoidAlgebra.single (Finsupp.single i 1) (1 : K)) = _
  rw [AddMonoidAlgebra.mapDomain_single, frontEmbed_single]
  rw [MvPolynomial.X_pow_eq_monomial]
  simp [MvPolynomial.X, MvPolynomial.monomial_mul]
  rfl

theorem frontLift_equiv (weights : Fin 4 → ℕ) (P : Poly4 K) :
    MvPolynomial.finSuccEquiv K 4 (frontLift K weights P) =
      weightedPolynomial K weights P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [frontLift_C, weightedPolynomial, MvPolynomial.finSuccEquiv_apply]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, map_mul, hP, frontLift_X, map_mul, map_pow,
        MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
      rw [map_mul]
      congr 1
      simp only [weightedPolynomial, MvPolynomial.eval₂Hom_X']
      exact mul_comm _ _

theorem weightedPolynomial_dvd_iff_support (weights : Fin 4 → ℕ) (m : ℕ) (P : Poly4 K) :
    Polynomial.X ^ m ∣ weightedPolynomial K weights P ↔
      ∀ d ∈ P.support, m ≤ Finsupp.weight weights d := by
  rw [← frontLift_equiv, Polynomial.X_pow_dvd_iff]
  constructor
  · intro h d hd
    by_contra hle
    have hin : frontEmbed weights d ∈ (frontLift K weights P).support := by
      rw [support_frontLift]
      exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have hc := h (Finsupp.weight weights d) (by omega)
    have hm : d ∈ ((MvPolynomial.finSuccEquiv K 4 (frontLift K weights P)).coeff
        (Finsupp.weight weights d)).support :=
      MvPolynomial.mem_support_coeff_finSuccEquiv.mpr hin
    simpa [hc] using hm
  · intro h n hn
    apply MvPolynomial.ext
    intro d
    rw [MvPolynomial.coeff_zero]
    by_contra hc
    have hm : d ∈ ((MvPolynomial.finSuccEquiv K 4 (frontLift K weights P)).coeff n).support :=
      MvPolynomial.mem_support_iff.mpr hc
    have hin := MvPolynomial.mem_support_coeff_finSuccEquiv.mp hm
    rw [support_frontLift] at hin
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hin
    have hw := congrArg (fun q : Fin 5 →₀ ℕ => q 0) heq
    have hw' : Finsupp.weight weights e = n := by simpa [frontEmbed] using hw
    have := h e he
    omega

theorem contactAtLeast_iff_support (x u0 u1 : K) (m : ℕ) (P : Poly4 K) :
    contactAtLeast K x u0 u1 m P ↔
      ∀ d ∈ (localize K x u0 u1 P).support,
        m ≤ Finsupp.weight ![1, 2, 0, 0] d := by
  exact weightedPolynomial_dvd_iff_support ![1, 2, 0, 0] m (localize K x u0 u1 P)

end
end ProximityUniversalReplacementV1

open ProximityUniversalReplacementV1
open MvPolynomial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem solution {K : Type*} [Field K] {I : Type*}
    (D w L s : ℕ) (m : I → ℕ) (nodes u0 u1 : I → K)
    (U : Poly4 K) (hU : U ≠ 0)
    (hne : ∃ Q : Poly4 K, Q ≠ 0 ∧ admissible K D w L s m nodes u0 u1 Q)
    (hdiv : ∀ Q : Poly4 K, admissible K D w L s m nodes u0 u1 Q → U ∣ Q)
    (P : Poly4 K)
    (hcontactWeight : weightedTotalDegree ![1, w, w - 1, 0] P ≤
      weightedTotalDegree ![1, w, w - 1, 0] U)
    (htotal : weightedTotalDegree ![0, 1, 1, 1] P ≤ weightedTotalDegree ![0, 1, 1, 1] U)
    (hslope : P.degreeOf 2 ≤ U.degreeOf 2)
    (objective : Fin 4 → ℕ)
    (hstrict : weightedTotalDegree objective P < weightedTotalDegree objective U)
    (hcontact : ∀ i, contactAtLeast K (nodes i) (u0 i) (u1 i)
      (min (m i) (contactOrder K (nodes i) (u0 i) (u1 i) U)) P) : P = 0 := by
  classical
  by_contra hP
  let good (Q : Poly4 K) : Prop := Q ≠ 0 ∧ admissible K D w L s m nodes u0 u1 Q
  have hex : ∃ n, ∃ Q, good Q ∧ weightedTotalDegree objective Q = n := by
    obtain ⟨Q, hQ⟩ := hne
    exact ⟨_, Q, hQ, rfl⟩
  obtain ⟨Q, hQ, hdegree⟩ := Nat.find_spec hex
  have hmin {A : Poly4 K} (hA : good A) :
      weightedTotalDegree objective Q ≤ weightedTotalDegree objective A := by
    rw [hdegree]
    exact Nat.find_min' hex ⟨A, hA, rfl⟩
  obtain ⟨V, hV⟩ := hdiv Q hQ.2
  have hVne : V ≠ 0 := by
    intro hz
    apply hQ.1
    simp [hV, hz]
  have hwt (weights : Fin 4 → ℕ) :
      weightedTotalDegree weights Q = weightedTotalDegree weights U + weightedTotalDegree weights V := by
    rw [hV]
    exact ProximityUniversalReplacementV1.weightedTotalDegree_mul weights U V hU hVne
  have hnew (weights : Fin 4 → ℕ) :
      weightedTotalDegree weights (P * V) = weightedTotalDegree weights P + weightedTotalDegree weights V :=
    ProximityUniversalReplacementV1.weightedTotalDegree_mul weights P V hP hVne
  have hQr : Q.degreeOf 2 = U.degreeOf 2 + V.degreeOf 2 := by
    rw [hV]
    exact MvPolynomial.degreeOf_mul_eq hU hVne
  have hPr : (P * V).degreeOf 2 = P.degreeOf 2 + V.degreeOf 2 :=
    MvPolynomial.degreeOf_mul_eq hP hVne
  obtain ⟨hD, hL, hs, hc⟩ := hQ.2
  have hgood : good (P * V) := by
    refine ⟨mul_ne_zero hP hVne, ?_, ?_, ?_, ?_⟩
    · have hq := hwt ![1, w, w - 1, 0]
      have hp := hnew ![1, w, w - 1, 0]
      omega
    · have hq := hwt ![0, 1, 1, 1]
      have hp := hnew ![0, 1, 1, 1]
      omega
    · omega
    · intro i
      apply (contactAtLeast_iff_le (nodes i) (u0 i) (u1 i) (m i) (P * V)
        (mul_ne_zero hP hVne)).mpr
      rw [contactOrder_mul _ _ _ P V hP hVne]
      have hq := (contactAtLeast_iff_le (nodes i) (u0 i) (u1 i) (m i) Q hQ.1).mp (hc i)
      rw [hV, contactOrder_mul _ _ _ U V hU hVne] at hq
      have hp := (contactAtLeast_iff_le (nodes i) (u0 i) (u1 i) _ P hP).mp (hcontact i)
      omega
  have hsmall := hmin hgood
  rw [hnew objective, hwt objective] at hsmall
  omega
