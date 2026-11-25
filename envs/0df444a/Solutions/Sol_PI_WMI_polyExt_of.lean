-- Prove2me | solution 1 for PI.WMI.polyExt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:31.964616+00:00
-- url     : https://prove2.me/submissions/33d11817-8816-4d7a-8eac-e0ffe7dff06f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_PolyExtLem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_PolyExt
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WMI_pe_evM_detPoly
import Theorems.Thm_PI_WMI_pe_left
import Theorems.Thm_PI_WMI_pe_mul_mem
import Theorems.Thm_PI_WMI_pe_one_mem
import Theorems.Thm_PI_WMI_pe_right
import Theorems.Thm_PI_WMI_pe_unitary_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
namespace PI.WMI
theorem _root_.solution (hp : PI.PolyCoef) (hu : PI.UnitaryDense) : PolyExt := by
  intro N H _ _ σ S hσ hfin hS
  classical
  let d := Module.finrank ℂ S
  let b : OrthonormalBasis (Fin d) ℂ S := stdOrthonormalBasis ℂ S
  have hc : ∀ i j : Fin d, ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ), ∀ g ∈ Kset (allPos N),
      inner ℂ ((b i : S) : H) (σ g ((b j : S) : H)) * g.det ^ k =
        MvPolynomial.eval (fun ij => g ij.1 ij.2) P :=
    fun i j => hp N H σ S hσ hfin hS ((b j : S) : H) (b j).2 ((b i : S) : H)
  choose k P hkP using hc
  let K : ℕ := ∑ p : Fin d × Fin d, k p.1 p.2
  have hk : ∀ i j, k i j ≤ K := fun i j =>
    Finset.single_le_sum (f := fun p : Fin d × Fin d => k p.1 p.2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (i, j))
  let Q : Fin d → Fin d → MvPolynomial (Fin N × Fin N) ℂ := fun i j => P i j * detPoly N ^ (K - k i j)
  have hQ : ∀ g ∈ Kset (allPos N), ∀ i j,
      evM g (Q i j) = g.det ^ K * ⟪((b i : S) : H), σ g ((b j : S) : H)⟫_ℂ := by
    intro g hg i j
    have e1 : evM g (Q i j) = evM g (P i j) * g.det ^ (K - k i j) := by
      rw [← pe_evM_detPoly g]
      simp only [Q, evM, map_mul, map_pow]
    rw [e1, show evM g (P i j) = _ from (hkP i j g hg).symm, mul_assoc, ← pow_add,
      Nat.add_sub_cancel' (hk i j), mul_comm]
  let Pm : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin d) (Fin d) ℂ := fun g => Matrix.of fun i j => evM g (Q i j)
  let Pl : Matrix (Fin N) (Fin N) ℂ → (S →ₗ[ℂ] S) := fun g => Matrix.toLin b.toBasis b.toBasis (Pm g)
  have hA : ∀ g ∈ Kset (allPos N), ∀ x : S, ((Pl g x : S) : H) = g.det ^ K • σ g (x : H) := by
    intro g hg x
    have key : S.subtype ∘ₗ Pl g = g.det ^ K • ((σ g : H →ₗ[ℂ] H) ∘ₗ S.subtype) := by
      refine b.toBasis.ext fun j => ?_
      have hmem : σ g ((b j : S) : H) ∈ S := hS g hg _ (b j).2
      have hsum := b.sum_repr' (⟨σ g ((b j : S) : H), hmem⟩ : S)
      have hsumH := congrArg (fun y : S => (y : H)) hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at hsumH
      show ((Matrix.toLin b.toBasis b.toBasis (Pm g) (b.toBasis j) : S) : H) =
        g.det ^ K • σ g ((b.toBasis j : S) : H)
      rw [Matrix.toLin_self]
      simp only [OrthonormalBasis.coe_toBasis, Submodule.coe_sum, Submodule.coe_smul, Pm, Matrix.of_apply]
      conv_rhs => rw [← hsumH]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hQ g hg i j, smul_smul]
    exact congrArg (fun f : S →ₗ[ℂ] H => f x) key
  have hPlmul : ∀ g ∈ Kset (allPos N), ∀ h ∈ Kset (allPos N), Pl (g * h) = Pl g ∘ₗ Pl h := by
    intro g hg h hh
    ext x
    rw [LinearMap.comp_apply, hA _ (pe_mul_mem hg hh), hA g hg, hA h hh, hσ.1.2 g hg h hh,
      ContinuousLinearMap.comp_apply, map_smul, smul_smul, Matrix.det_mul, mul_pow]
  have hB : ∀ g ∈ Kset (allPos N), ∀ h ∈ Kset (allPos N), Pm (g * h) = Pm g * Pm h := by
    intro g hg h hh
    apply (Matrix.toLin b.toBasis b.toBasis).injective
    rw [Matrix.toLin_mul b.toBasis b.toBasis b.toBasis]
    exact hPlmul g hg h hh
  have hC1 : ∀ h ∈ Kset (allPos N), ∀ g, Pm (g * h) = Pm g * Pm h := by
    intro h hh g
    ext i j
    obtain ⟨Q', hQ'⟩ := pe_right h (Q i j)
    let D := Q' - ∑ r, Q i r * C (Pm h r j)
    have hD : ∀ g', evM g' D = (Pm (g' * h) - Pm g' * Pm h) i j := by
      intro g'
      simp only [D, evM, map_sub, map_sum, map_mul, eval_C] at hQ' ⊢
      rw [hQ']
      simp [Pm, evM, Matrix.mul_apply]
    have hD0 : D = 0 := hu N D fun u hu' => by
      rw [← evM, hD u, hB u (pe_unitary_mem u hu') h hh, sub_self, Matrix.zero_apply]
    have := hD g
    rw [hD0] at this
    simp only [evM, map_zero, Matrix.sub_apply] at this
    exact sub_eq_zero.mp this.symm
  have hC2 : ∀ g h, Pm (g * h) = Pm g * Pm h := by
    intro g h
    ext i j
    obtain ⟨Q', hQ'⟩ := pe_left g (Q i j)
    let D := Q' - ∑ r, C (Pm g i r) * Q r j
    have hD : ∀ h', evM h' D = (Pm (g * h') - Pm g * Pm h') i j := by
      intro h'
      simp only [D, evM, map_sub, map_sum, map_mul, eval_C] at hQ' ⊢
      rw [hQ']
      simp [Pm, evM, Matrix.mul_apply]
    have hD0 : D = 0 := hu N D fun u hu' => by
      rw [← evM, hD u, hC1 u (pe_unitary_mem u hu') g, sub_self, Matrix.zero_apply]
    have := hD h
    rw [hD0] at this
    simp only [evM, map_zero, Matrix.sub_apply] at this
    exact sub_eq_zero.mp this.symm
  refine ⟨K, Pl, ⟨?_, ?_, ?_⟩, hA⟩
  · intro g h
    show Matrix.toLin b.toBasis b.toBasis (Pm (g * h)) = _
    rw [hC2, Matrix.toLin_mul b.toBasis b.toBasis b.toBasis]
  · ext x
    rw [hA 1 (pe_one_mem N), hσ.1.1]
    simp
  · intro x y
    let fL : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ :=
      (innerₛₗ ℂ y).comp ((LinearMap.applyₗ x).comp (Matrix.toLin b.toBasis b.toBasis).toLinearMap)
    refine ⟨∑ i, ∑ j, Q i j * C (fL (Matrix.single i j 1)), fun g => ?_⟩
    have hf : ⟪y, Pl g x⟫_ℂ = fL (Pm g) := rfl
    rw [hf, Matrix.matrix_eq_sum_single (Pm g)]
    simp only [map_sum, evM, map_mul, eval_C]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show Matrix.single i j (Pm g i j) = Pm g i j • Matrix.single i j (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
    rfl
end PI.WMI
