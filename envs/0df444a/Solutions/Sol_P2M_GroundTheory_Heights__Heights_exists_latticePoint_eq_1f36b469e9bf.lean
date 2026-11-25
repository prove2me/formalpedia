-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_latticePoint_eq_1f36b469e9bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:56:34.440072+00:00
-- url     : https://prove2.me/submissions/e381eaaa-f03e-4067-ad89-e3b780cabe8b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockPoints
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_int_comb_c953859cc094
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_embedding_of_mul_c069f2dba8a6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_latticeForm_add_e2e620659c05
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_latticeForm_single_8e16640cd985
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_latticeMap_intComb_ac9dfce53bdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable {r N : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) {z : Cone (fun _ : Unit ↦ N) ℂ}
    (hz : z ∈ conePoints (latticeIdeal φ) ℂ) :
    ∃ (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ), w ≠ 0 ∧ z = latticePoint φ σ w := by
  choose D hD c hc using exists_int_comb hφ
  let ev : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ →+* ℂ :=
    eval₂Hom (Int.castRingHom ℂ) fun v ↦ z v.1 v.2
  have key : ∀ f, latticeMap φ f = 0 → ev f = 0 := fun f hf ↦ hz.2 f hf
  let P : (Fin (r + 1) → K) → MvPolynomial (Coord fun _ : Unit ↦ N) ℤ :=
    fun v ↦ ∑ b, (c v b : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) * X ⟨(), b⟩
  have hP : ∀ v, latticeMap φ (P v) = (D v : MvPolynomial (Fin (r + 1)) K) * latticeForm v := by
    intro v
    have h := congrArg latticeForm (hc v)
    simp only [P, latticeMap_intComb, h]
    let Lf : (Fin (r + 1) → K) →+ MvPolynomial (Fin (r + 1)) K :=
      AddMonoidHom.mk' latticeForm latticeForm_add
    rw [← zsmul_eq_mul]
    exact map_zsmul Lf (D v) v
  have hDc : ∀ v, (D v : ℂ) ≠ 0 := fun v ↦ Int.cast_ne_zero.mpr (hD v)
  let L : (Fin (r + 1) → K) → ℂ := fun v ↦ ev (P v) / D v
  have hE : ∀ v, ev (P v) = D v * L v := fun v ↦ by
    simp only [L]
    field_simp [hDc v]
  have hadd : ∀ u v, L (u + v) = L u + L v := by
    intro u v
    have h := key ((D u * D v : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) * P (u + v) -
      (D (u + v) * D v : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) * P u -
      (D (u + v) * D u : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) * P v) (by
        simp only [map_sub, map_mul, map_intCast, hP, latticeForm_add]
        ring)
    simp only [map_sub, map_mul, map_intCast, hE] at h
    have h' : ((D u * D v * D (u + v) : ℤ) : ℂ) * (L (u + v) - (L u + L v)) = 0 := by
      push_cast
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left
      (Int.cast_ne_zero.mpr (mul_ne_zero (mul_ne_zero (hD u) (hD v)) (hD (u + v)))))
  have hmul : ∀ (j j' : Fin (r + 1)) (a b a' b' : K), a * b = a' * b' →
      L (Pi.single j a) * L (Pi.single j' b) = L (Pi.single j a') * L (Pi.single j' b') := by
    intro j j' a b a' b' hab
    have hC : (C a * C b : MvPolynomial (Fin (r + 1)) K) = C a' * C b' := by
      rw [← C_mul, ← C_mul, hab]
    have h := key
      ((D (Pi.single j a') * D (Pi.single j' b') : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) *
          (P (Pi.single j a) * P (Pi.single j' b)) -
        (D (Pi.single j a) * D (Pi.single j' b) : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) *
          (P (Pi.single j a') * P (Pi.single j' b'))) (by
        simp only [map_sub, map_mul, map_intCast, hP, latticeForm_single]
        linear_combination
          ((D (Pi.single j a') * D (Pi.single j' b') * D (Pi.single j a) * D (Pi.single j' b) :
            MvPolynomial (Fin (r + 1)) K) * X j * X j') * hC)
    simp only [map_sub, map_mul, map_intCast, hE] at h
    have h' : ((D (Pi.single j a) * D (Pi.single j' b) * D (Pi.single j a') * D (Pi.single j' b') : ℤ) : ℂ) *
        (L (Pi.single j a) * L (Pi.single j' b) - L (Pi.single j a') * L (Pi.single j' b')) = 0 := by
      push_cast
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left (Int.cast_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (hD _) (hD _)) (hD _)) (hD _))))
  have hφb : ∀ b, L (φ b) = z () b := by
    intro b
    have h := key (P (φ b) - (D (φ b) : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) * X ⟨(), b⟩) (by
      simp only [map_sub, map_mul, map_intCast, hP]
      simp [latticeMap])
    simp only [map_sub, map_mul, map_intCast, hE] at h
    have h' : (D (φ b) : ℂ) * (L (φ b) - z () b) = 0 := by
      simp only [ev, eval₂Hom_X'] at h
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left (hDc _))
  have hne : ∃ v, L v ≠ 0 := by
    obtain ⟨b, hb⟩ : ∃ b, z () b ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hz.1 () (funext hcon)
    exact ⟨φ b, by rw [hφb]; exact hb⟩
  obtain ⟨σ, w, hw, hL⟩ := exists_embedding_of_mul L hadd hmul hne
  refine ⟨σ, w, hw, ?_⟩
  funext u b
  rw [← hφb b, hL]
  rfl
end GroundTheory.Heights₂.Heights
