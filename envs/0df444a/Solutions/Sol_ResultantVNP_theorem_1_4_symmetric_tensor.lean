-- Prove2me | solution 1 for ResultantVNP.theorem_1_4_symmetric_tensor
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T11:00:35.938202+00:00
-- url     : https://prove2.me/submissions/1af560f9-1f67-4f4a-8daf-5068f1f026e2

import Mathlib
import Definitions.Def_ResultantVNP_charCoeff
import Theorems.Thm_ResultantVNP_circuit_affine_coefficient_bound
import Theorems.Thm_ResultantVNP_hardness_circuit_collapse
import Theorems.Thm_ResultantVNP_theorem_3_2

set_option autoImplicit false

namespace SymmetricHardness
open ResultantVNP MvPolynomial

private def PB (f : ℕ → ℕ) : Prop := ∃ a b : ℕ, ∀ n, f n ≤ a * (n+1)^b

private lemma pb_of_poly {f : ℕ → ℕ} (h : PolyBounded f) : PB f := by
  obtain ⟨c,hc⟩ := h
  refine ⟨2*c,c,fun n => (hc n).trans ?_⟩
  have hp : n^c ≤ (n+1)^c := Nat.pow_le_pow_left (by omega) c
  have hp1 : 1 ≤ (n+1)^c := Nat.one_le_pow c (n+1) (by omega)
  nlinarith

private lemma poly_of_pb {f : ℕ → ℕ} (h : PB f) : PolyBounded f := by
  obtain ⟨a,b,h⟩ := h
  let c := a * 2^b+b
  refine ⟨c,fun n => ?_⟩
  by_cases hn : n = 0
  · subst n
    have hh := h 0
    simp only [zero_add, one_pow, mul_one] at hh
    have hp : 1 ≤ 2^b := Nat.one_le_pow b 2 (by omega)
    have ha := Nat.mul_le_mul_left a hp
    simp only [mul_one] at ha
    dsimp [c]
    omega
  · have hn1 : 1 ≤ n := by omega
    have hp : (n+1)^b ≤ (2*n)^b := Nat.pow_le_pow_left (by omega) b
    rw [mul_pow] at hp
    have hbc : b ≤ c := by dsimp [c]; omega
    have hp' : n^b ≤ n^c := Nat.pow_le_pow_right hn1 hbc
    have ha : a*2^b ≤ c := by dsimp [c]; omega
    calc
      f n ≤ a*(n+1)^b := h n
      _ ≤ a*(2^b*n^b) := Nat.mul_le_mul_left a hp
      _ = (a*2^b)*n^b := by ring
      _ ≤ c*n^c := Nat.mul_le_mul ha hp'
      _ ≤ c*n^c+c := by omega

private lemma pb_const (c : ℕ) : PB (fun _ => c) := ⟨c,0,by simp⟩
private lemma pb_id : PB (fun n => n) := ⟨1,1,by simp⟩

private lemma pb_add {f g : ℕ → ℕ} (hf : PB f) (hg : PB g) :
    PB (fun n => f n + g n) := by
  obtain ⟨a,b,hf⟩ := hf
  obtain ⟨c,d,hg⟩ := hg
  refine ⟨a+c,b+d,fun n => ?_⟩
  have hb : (n+1)^b ≤ (n+1)^(b+d) := Nat.pow_le_pow_right (by omega) (by omega)
  have hd : (n+1)^d ≤ (n+1)^(b+d) := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    f n + g n ≤ a*(n+1)^b + c*(n+1)^d := Nat.add_le_add (hf n) (hg n)
    _ ≤ a*(n+1)^(b+d) + c*(n+1)^(b+d) :=
      Nat.add_le_add (Nat.mul_le_mul_left a hb) (Nat.mul_le_mul_left c hd)
    _ = (a+c)*(n+1)^(b+d) := by ring

private lemma pb_mul {f g : ℕ → ℕ} (hf : PB f) (hg : PB g) :
    PB (fun n => f n * g n) := by
  obtain ⟨a,b,hf⟩ := hf
  obtain ⟨c,d,hg⟩ := hg
  refine ⟨a*c,b+d,fun n => ?_⟩
  calc
    f n*g n ≤ (a*(n+1)^b)*(c*(n+1)^d) := Nat.mul_le_mul (hf n) (hg n)
    _ = (a*c)*(n+1)^(b+d) := by rw [pow_add]; ring

private lemma pb_pow {f : ℕ → ℕ} (hf : PB f) (k : ℕ) : PB (fun n => f n^k) := by
  obtain ⟨a,b,hf⟩ := hf
  refine ⟨a^k,b*k,fun n => ?_⟩
  calc
    f n^k ≤ (a*(n+1)^b)^k := Nat.pow_le_pow_left (hf n) k
    _ = a^k*(n+1)^(b*k) := by rw [mul_pow,pow_mul]

private lemma pb_mono {f g : ℕ → ℕ} (hg : PB g) (h : ∀ n, f n ≤ g n) : PB f := by
  obtain ⟨a,b,hg⟩ := hg
  exact ⟨a,b,fun n => (h n).trans (hg n)⟩

private lemma poly_mono {f g : ℕ → ℕ} (hg : PolyBounded g) (h : ∀ n, f n ≤ g n) :
    PolyBounded f := poly_of_pb (pb_mono (pb_of_poly hg) h)

private noncomputable def delta (n : ℕ) (T : Sym (Fin n) 3) : ℤ :=
  if ∃ j, T = Sym.replicate 3 j then 1 else 0

private noncomputable def affine {σ R : Type} [CommRing R] (δ : σ → ℤ) (T : σ) :
    Polynomial (MvPolynomial σ R) :=
  Polynomial.C (C (δ T : R)) + Polynomial.X * Polynomial.C (X T)

private lemma lift_charPoly {σ : Type} (δ : σ → ℤ) (p : MvPolynomial σ ℤ) :
    Polynomial.map (map (Int.castRingHom ℂ)) (aeval (affine (R := ℤ) δ) p) =
      aeval (affine (R := ℂ) δ) (map (Int.castRingHom ℂ) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [affine]
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | mul_X p i hp => simp [affine, hp]

private lemma charCoeff_complex (𝓡 : ResultantSystem) (n s : ℕ) :
    map (Int.castRingHom ℂ) (charCoeff 𝓡 n s) =
      (aeval (affine (R := ℂ) (delta n))
        (map (Int.castRingHom ℂ) (symTensorDet 𝓡 n))).coeff s := by
  classical
  have h := lift_charPoly (delta n) (symTensorDet 𝓡 n)
  have hfun : affine (R := ℤ) (delta n) =
      (fun T : Sym (Fin n) 3 =>
        Polynomial.C (if ∃ j, T = Sym.replicate 3 j then (1 : MvPolynomial (Sym (Fin n) 3) ℤ) else 0) +
          Polynomial.X * Polynomial.C (X T)) := by
    funext T
    by_cases hT : ∃ j, T = Sym.replicate 3 j <;> simp [affine, delta, hT]
  rw [hfun] at h
  have hc := congrArg (fun p => p.coeff s) h
  simpa only [Polynomial.coeff_map, charCoeff] using hc


private lemma coefficient_circuits (𝓡 : ResultantSystem)
    (h : HasPolySizeCircuits (fun n => map (Int.castRingHom ℂ) (symTensorDet 𝓡 n))) :
    HasPolySizeCircuits (fun m => map (Int.castRingHom ℂ)
      (charCoeff 𝓡 (5*m^2) (m^2))) := by
  obtain ⟨c,hc⟩ := h
  have hm2 : PB (fun m => m^2) := pb_pow pb_id 2
  have hn : PB (fun m => 5*m^2) := pb_mul (pb_const 5) hm2
  have hbase : PB (fun m => c*(5*m^2)^c+c) :=
    pb_add (pb_mul (pb_const c) (pb_pow hn c)) (pb_const c)
  have hsize : PolyBounded (fun m => 2*(m^2+1)^2*(c*(5*m^2)^c+c)+1) :=
    poly_of_pb (pb_add (pb_mul (pb_mul (pb_const 2)
      (pb_pow (pb_add hm2 (pb_const 1)) 2)) hbase) (pb_const 1))
  obtain ⟨b,hb⟩ := hsize
  refine ⟨b,fun m hm => ?_⟩
  have hdim : 1 ≤ 5*m^2 := by nlinarith
  obtain ⟨C,hval,hCs⟩ := hc (5*m^2) hdim
  change C.value = map (Int.castRingHom ℂ) (symTensorDet 𝓡 (5*m^2)) at hval
  obtain ⟨D,hD,hDs⟩ := circuit_affine_coefficient_bound C
    (fun T => (delta (5*m^2) T : ℂ)) (m^2)
  refine ⟨D, ?_, le_trans (le_trans hDs ?_) (hb m)⟩
  · change D.value = map (Int.castRingHom ℂ) (charCoeff 𝓡 (5*m^2) (m^2))
    rw [charCoeff_complex]
    change D.value = (aeval (affine (delta (5*m^2)))
      (map (Int.castRingHom ℂ) (symTensorDet 𝓡 (5*m^2)))).coeff (m^2)
    unfold affine
    rw [← hval]
    exact hD
  · exact Nat.add_le_add_right (Nat.mul_le_mul_left (2*(m^2+1)^2) hCs) 1

end SymmetricHardness

theorem solution (𝓡 : ResultantVNP.ResultantSystem)
    (h : ResultantVNP.HasPolySizeCircuits (fun n =>
      MvPolynomial.map (Int.castRingHom ℂ) (ResultantVNP.symTensorDet 𝓡 n))) :
    ResultantVNP.VP = ResultantVNP.VNP := by
  apply ResultantVNP.hardness_circuit_collapse
    (fun m => MvPolynomial.map (Int.castRingHom ℂ)
      (ResultantVNP.charCoeff 𝓡 (5*m^2) (m^2))) 3 (by omega)
  · exact (ResultantVNP.theorem_3_2 𝓡).1
  · exact SymmetricHardness.coefficient_circuits 𝓡 h

#print axioms solution
