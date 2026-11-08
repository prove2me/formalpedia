-- Prove2me | solution 1 for TeleportGates.Ck.pauliFrame_mem_pauliGroup
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:30:37.231181+00:00
-- url     : https://prove2.me/submissions/b771956c-bfbd-4690-8fa1-63bc8a50fb55

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_QECC
import Definitions.Def_TeleportGates_Ck_pauliFrame

namespace Aux_Teleport_pf
open QAlgorithms QAlgorithms.Stabilizer

noncomputable def fw (x z : Bool) : Matrix Bool Bool ℂ :=
  (if x then pauliX else 1) * (if z then pauliZ else 1)

def ow (x z : Bool) : Pauli :=
  if x then (if z then Pauli.Y else Pauli.X) else (if z then Pauli.Z else Pauli.I)

noncomputable def sw (x z : Bool) : ℂ := if x && z then -Complex.I else 1

lemma fw_eq (x z : Bool) (β γ : Bool) : fw x z β γ = sw x z * (ow x z).mat β γ := by
  cases x <;> cases z <;> cases β <;> cases γ <;>
    simp [fw, sw, ow, Pauli.mat, pauliX, pauliZ, pauliY, Matrix.mul_apply, Fintype.sum_bool]

lemma fw_unitary (x z : Bool) (β γ : Bool) :
    ∑ δ : Bool, star (fw x z δ β) * fw x z δ γ = if β = γ then 1 else 0 := by
  cases x <;> cases z <;> cases β <;> cases γ <;>
    simp [fw, pauliX, pauliZ, Matrix.mul_apply, Fintype.sum_bool]

lemma I_pow_mod (m : ℕ) : Complex.I ^ (m % 4) = Complex.I ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

end Aux_Teleport_pf

open QAlgorithms QAlgorithms.Stabilizer TeleportGates.Ck Aux_Teleport_pf in
theorem solution (n : ℕ) (x z : Qubits n) :
    ∃ h : pauliFrame n x z ∈ Matrix.unitaryGroup (Qubits n) ℂ,
      (⟨pauliFrame n x z, h⟩ : Matrix.unitaryGroup (Qubits n) ℂ) ∈ pauliGroup n := by
  classical
  have hPF : ∀ c a, pauliFrame n x z c a = ∏ i, fw (x i) (z i) (c i) (a i) := by
    intro c a; rfl
  have hU : pauliFrame n x z ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext c a
    rw [Matrix.mul_apply]
    simp only [Matrix.star_apply, hPF, star_prod]
    rw [show (∑ b : Qubits n, (∏ i, star (fw (x i) (z i) (b i) (c i))) *
        ∏ i, fw (x i) (z i) (b i) (a i))
        = ∑ b : Qubits n, ∏ i, (star (fw (x i) (z i) (b i) (c i)) * fw (x i) (z i) (b i) (a i)) by
      simp only [Finset.prod_mul_distrib]]
    rw [← Fintype.prod_sum (fun i δ => star (fw (x i) (z i) δ (c i)) * fw (x i) (z i) δ (a i))]
    simp only [fw_unitary, Matrix.one_apply]
    by_cases hca : c = a
    · subst hca; simp
    · rw [if_neg hca]
      obtain ⟨i, hi⟩ : ∃ i, c i ≠ a i := by
        by_contra h; push_neg at h; exact hca (funext h)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  refine ⟨hU, Subgroup.subset_closure ?_⟩
  let k := (Finset.univ.filter (fun i => x i && z i)).card
  refine ⟨⟨((3 * k : ℕ) : ZMod 4), fun i => ow (x i) (z i)⟩, ?_⟩
  ext c a
  simp only [PauliString.toMatrix, Matrix.of_apply]
  show pauliFrame n x z c a = _
  rw [hPF]
  simp only [fw_eq, Finset.prod_mul_distrib]
  congr 1
  rw [ZMod.val_natCast, I_pow_mod, pow_mul]
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]; ring
  rw [hI3]
  simp only [sw]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
