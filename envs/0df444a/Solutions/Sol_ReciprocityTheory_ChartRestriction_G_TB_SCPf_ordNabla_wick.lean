-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.ordNabla_wick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:33:59.506049+00:00
-- url     : https://prove2.me/submissions/12cea2c8-f430-416a-9ca7-53668202197f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondOrderIterateEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCWick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_betaH_zero_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_betaH_antisymm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_kapW_supp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_delta_pow_rename
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_bracket
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_ordNabla_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_side_inl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_side_inr
import Theorems.Thm_wick_formula


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι : Type}
    [Fintype ι] (s : ι → Bool) (ξa ξb : ι → (Fin d → k) × (Fin d → k)) (hb0 : ∀ l, (ξb l).1 = 0)
    (haa : ∀ l l', s l = s l' → betaH k (ξa l) (ξa l') = 0)
    (hab : ∀ l l', s l = s l' → betaH k (ξa l) (ξb l') = 0) (P : MvPolynomial ι k) (f : PS k 1 d) :
    ordNabla k B h m s (fun l => ξa l + ξb l) P (liftX k f) =
      ∑ n ∈ Finset.range ((MvPolynomial.rename (sideE s) P).totalDegree + 1),
        PI.WickFormula.ordEval (opL B h m s ξa) (opR B h m s ξa)
          (((n.factorial : ℚ)⁻¹) • MvPolynomial.rename (sideE s) ((secondOrder k (kapW m s ξa ξb))^[n] P))
          (liftX k f) := by
  have hbb : ∀ l l', betaH k (ξb l) (ξb l') = 0 := fun l l' => by
    rw [show ξb l = (0, (ξb l).2) from Prod.ext (hb0 l) rfl, show ξb l' = (0, (ξb l').2) from Prod.ext (hb0 l') rfl]
    exact betaH_zero_zero _ _
  have hba : ∀ l l', s l = s l' → betaH k (ξb l) (ξa l') = 0 := fun l l' e => by
    rw [betaH_antisymm, hab l' l e.symm, neg_zero]
  have cA : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l).1 (ξa l).2) (nablaL B h m (ξa l').1 (ξa l').2) :=
    fun l l' e => nablaL_comm hN2 B h m _ _ (haa l l' e)
  have cAB : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l).1 (ξa l).2) (nablaL B h m (ξb l').1 (ξb l').2) :=
    fun l l' e => nablaL_comm hN2 B h m _ _ (hab l l' e)
  have cBA : ∀ l l', s l = s l' → Commute (nablaL B h m (ξb l).1 (ξb l).2) (nablaL B h m (ξa l').1 (ξa l').2) :=
    fun l l' e => nablaL_comm hN2 B h m _ _ (hba l l' e)
  have cB : ∀ l l', Commute (nablaL B h m (ξb l).1 (ξb l).2) (nablaL B h m (ξb l').1 (ξb l').2) :=
    fun l l' => nablaL_comm hN2 B h m _ _ (hbb l l')
  have hsum : ∀ l, nablaL B h m (ξa l + ξb l).1 (ξa l + ξb l).2 =
      nablaL B h m (ξa l).1 (ξa l).2 + nablaL B h m (ξb l).1 (ξb l).2 := fun l =>
    nablaL_add B h m _ _ _ _
  have cAll : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l + ξb l).1 (ξa l + ξb l).2)
      (nablaL B h m (ξa l' + ξb l').1 (ξa l' + ξb l').2) := fun l l' e => by
    rw [hsum, hsum]
    exact ((cA l l' e).add_right (cAB l l' e)).add_left ((cBA l l' e).add_right (cB l l'))
  rw [ordNabla_eq B h m s (fun l => ξa l + ξb l) cAll P (liftX k f)]
  have hL : opL B h m s (fun l => ξa l + ξb l) = opL B h m s ξa + opL B h m s ξb := funext fun i => hsum _
  have hR : opR B h m s (fun l => ξa l + ξb l) = opR B h m s ξa + opR B h m s ξb := funext fun j => hsum _
  have key := _root_.wick_formula k (Module.End k (AA k d)) (AA k d) _ _ (opL B h m s ξa) (opL B h m s ξb)
    (opR B h m s ξa) (opR B h m s ξb) (kapE s (kapW m s ξa ξb)) (liftX k f)
    (fun i i' => ⟨cA _ _ (by rw [side_inl s i, side_inl s i']), cAB _ _ (by rw [side_inl s i, side_inl s i']),
      cB _ _⟩)
    (fun j j' => ⟨cA _ _ (by rw [side_inr s j, side_inr s j']), cAB _ _ (by rw [side_inr s j, side_inr s j']),
      cB _ _⟩)
    (fun i j => cB _ _)
    (fun i j => by
      rw [nablaL_bracket hN2 B h m]
      unfold kapE kapW
      rw [if_pos ⟨side_inl s i, side_inr s j⟩])
    (fun i => by
      rw [Module.End.smul_def, opL, hb0]
      exact hN3 R d O k B h m _ f)
    (fun j => by
      rw [Module.End.smul_def, opR, hb0]
      exact hN3 R d O k B h m _ f)
    (MvPolynomial.rename (sideE s) P)
  rw [hL, hR, ← Module.End.smul_def, key]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Module.End.smul_def, delta_pow_rename s _ (kapW_supp m s ξa ξb)]
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
