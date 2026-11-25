-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.glob_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:45:33.133458+00:00
-- url     : https://prove2.me/submissions/f7b04532-1e9a-4e35-82e7-00aad7b55b1b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_GmapLeLocS
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
section Glob
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V] {M : ℕ}
private theorem sum_mem_crdOf (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {ι : Type}
    (t : Finset ι) (z : ι → Fin M → E) (hz : ∀ i ∈ t, z i ∈ crdOf b L0) :
    ∑ i ∈ t, z i ∈ crdOf b L0 := by
  show ∑ j, (∑ i ∈ t, z i) j • b j ∈ L0
  simp only [Finset.sum_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact L0.sum_mem fun i hi => hz i hi
private theorem algebraMap_smul_mem_crdOf (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (s : 𝓞 E)
    {x : Fin M → E} (hx : x ∈ crdOf b L0) : (algebraMap (𝓞 E) E s) • x ∈ crdOf b L0 := by
  show ∑ j, ((algebraMap (𝓞 E) E s) • x) j • b j ∈ L0
  have h := L0.smul_mem s (show ∑ j, x j • b j ∈ L0 from hx)
  rw [Finset.smul_sum] at h
  convert h using 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_smul, algebraMap_smul]
private theorem add_mem_crdOf (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V)
    {x y : Fin M → E} (hx : x ∈ crdOf b L0) (hy : y ∈ crdOf b L0) : x + y ∈ crdOf b L0 := by
  show ∑ j, (x + y) j • b j ∈ L0
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  exact L0.add_mem hx hy
end Glob
end PI.UnitaryGroupMassFormula.UJClassMass
end
end

set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory PI.UnitaryGroupMassFormula.UJClassFin
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V] {M : ℕ}
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {F : Type} [Field F] [Algebra F E] (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V)
    {u k : ℕ} (hu : ∀ x ∈ crdOf b L0, ∀ i, IsIntegral ℤ ((u : F) • x i))
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ crdOf b L0)
    (Y : Matrix (Fin M) (Fin M) E) (s : 𝓞 E) (e : Fin M → Fin M → E) (he : ∀ i j, IsIntegral ℤ (e i j))
    (hY : ∀ i j, (algebraMap (𝓞 E) E s) * (Y - 1) i j = ((u * k : ℕ) : E) * e i j)
    {x : Fin M → E} (hx : x ∈ crdOf b L0) : (algebraMap (𝓞 E) E s) • Y.mulVec x ∈ crdOf b L0 := by
  have key : ∀ i0, (algebraMap (𝓞 E) E s) * (Y.mulVec x) i0 =
      (algebraMap (𝓞 E) E s) * x i0 + ∑ j, ((k : F) • (e i0 j * ((u : F) • x j))) := by
    intro i0
    have hsplit : ∀ j, (algebraMap (𝓞 E) E s) * Y i0 j =
        ((u * k : ℕ) : E) * e i0 j + (algebraMap (𝓞 E) E s) * (1 : Matrix (Fin M) (Fin M) E) i0 j := by
      intro j
      have hj := hY i0 j
      rw [Matrix.sub_apply, mul_sub] at hj
      linear_combination hj
    show (algebraMap (𝓞 E) E s) * ∑ j, Y i0 j * x j = _
    simp only [Finset.mul_sum, ← mul_assoc, hsplit, add_mul, Finset.sum_add_distrib, Matrix.one_apply,
      mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Algebra.smul_def, map_natCast]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hvec : (algebraMap (𝓞 E) E s) • Y.mulVec x = (algebraMap (𝓞 E) E s) • x +
      ∑ i, ∑ j, Pi.single i ((k : F) • (e i j * ((u : F) • x j))) := by
    funext i0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [key i0]
    congr 1
    simp only [Finset.sum_apply, Pi.single_apply]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hvec]
  exact add_mem_crdOf b L0 (algebraMap_smul_mem_crdOf b L0 s hx)
    (sum_mem_crdOf b L0 _ _ fun i _ => sum_mem_crdOf b L0 _ _ fun j _ =>
      hk i _ ((he i j).mul (hu x hx j)))
end PI.UnitaryGroupMassFormula.UJClassMass
