-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.cubicPairing_combinedWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:43:33.994186+00:00
-- url     : https://prove2.me/submissions/9432c995-4090-4ebf-8c6e-d968dbdcfa68

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] primeQuditRegisterLabelFintype
open QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site]
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily._p2m_local_instance_d01bce0bd8_633
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily._p2m_local_instance_d01bce0bd8_634
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily._p2m_local_instance_d01bce0bd8_635
namespace QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
theorem _root_.solution (R : CubicRowFamily p Logical Stabilizer Site)
    (q r s : Logical ⊕ Stabilizer → ZMod p) :
    cubicPairing p (R.combinedWord q) (R.combinedWord r) (R.combinedWord s) =
      ∑ a : Logical ⊕ Stabilizer, ∑ b : Logical ⊕ Stabilizer,
        ∑ c : Logical ⊕ Stabilizer, q a * r b * s c * cubicPairing p (R.row a) (R.row b) (R.row c) := by
  classical
  unfold cubicPairing combinedWord
  simp only [Pi.smul_apply, Finset.sum_apply]
  have expand (site : Site) :
      (∑ a, q a * R.row a site) * (∑ b, r b * R.row b site) *
          (∑ c, s c * R.row c site) =
        ∑ a, ∑ b, ∑ c,
          (q a * R.row a site) * (r b * R.row b site) * (s c * R.row c site) := by
    rw [Finset.sum_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    calc
      (q a * R.row a site * ∑ b, r b * R.row b site) *
          ∑ c, s c * R.row c site =
        ∑ c, (q a * R.row a site * ∑ b, r b * R.row b site) *
          (s c * R.row c site) := by rw [Finset.mul_sum]
      _ = ∑ c, ∑ b,
          (q a * R.row a site) * (r b * R.row b site) * (s c * R.row c site) := by
        apply Finset.sum_congr rfl
        intro c _
        calc
          (q a * R.row a site * ∑ b, r b * R.row b site) *
              (s c * R.row c site) =
              q a * R.row a site *
                ((∑ b, r b * R.row b site) * (s c * R.row c site)) := by ring
          _ = q a * R.row a site * ∑ b,
              (r b * R.row b site) * (s c * R.row c site) := by rw [Finset.sum_mul]
          _ = ∑ b, q a * R.row a site *
              ((r b * R.row b site) * (s c * R.row c site)) := by rw [Finset.mul_sum]
          _ = ∑ b,
              (q a * R.row a site) * (r b * R.row b site) *
                (s c * R.row c site) := by
              apply Finset.sum_congr rfl
              intro b _
              ring
      _ = ∑ b, ∑ c,
          (q a * R.row a site) * (r b * R.row b site) * (s c * R.row c site) := by
        exact Finset.sum_comm
  calc
    (∑ site,
        (∑ a, q a * R.row a site) * (∑ b, r b * R.row b site) *
          (∑ c, s c * R.row c site)) =
        ∑ site, ∑ a, ∑ b, ∑ c,
          (q a * R.row a site) * (r b * R.row b site) * (s c * R.row c site) := by
      apply Finset.sum_congr rfl
      intro site _
      exact expand site
    _ = ∑ a : Logical ⊕ Stabilizer, ∑ b : Logical ⊕ Stabilizer,
        ∑ c : Logical ⊕ Stabilizer, ∑ site : Site,
          q a * r b * s c * (R.row a site * R.row b site * R.row c site) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro site _
      ring
    _ = ∑ a : Logical ⊕ Stabilizer, ∑ b : Logical ⊕ Stabilizer,
        ∑ c : Logical ⊕ Stabilizer, q a * r b * s c *
          (∑ site : Site, R.row a site * R.row b site * R.row c site) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]
end QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
