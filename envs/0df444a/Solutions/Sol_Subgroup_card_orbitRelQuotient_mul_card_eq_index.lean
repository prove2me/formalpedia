-- Prove2me | solution 1 for Subgroup.card_orbitRelQuotient_mul_card_eq_index
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/499349aa-7fe9-5213-80bc-5e6fd1b94016

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subgroup_card_orbitRelQuotient_mul_card_eq_index

set_option autoImplicit false

open Subgroup MulAction

namespace GroupTheory

namespace FreeDoubleCoset

variable {M : Type*} [Group M]

def ConjTrivial (K H : Subgroup M) : Prop :=
  ∀ g x : M, x ∈ K → g⁻¹ * x * g ∈ H → x = 1

theorem stabilizer_eq_bot_of_conjTrivial (K H : Subgroup M) (hKH : ConjTrivial K H) (q : M ⧸ H) :
    MulAction.stabilizer K q = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  induction q using QuotientGroup.induction_on with
  | H g =>
    have hmem : (a : M) • (g : M ⧸ H) = (g : M ⧸ H) := ha
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq, smul_eq_mul, mul_inv_rev] at hmem
    have hinv : (a : M)⁻¹ = 1 := hKH g ((a : M)⁻¹) (inv_mem a.2) hmem
    have : (a : M) = 1 := by rw [← inv_inv (a : M), hinv, inv_one]
    exact Subgroup.mem_bot.mpr (Subtype.ext this)

section DoubleCoset

variable (H K : Subgroup M)

theorem mk''_mk_inv_eq {g g' : M} (η : M) (hη : η ∈ H) (hk : g'⁻¹ * η⁻¹ * g ∈ K) :
    (Quotient.mk'' ((g⁻¹ : M) : M ⧸ H) : orbitRel.Quotient K (M ⧸ H)) =
      Quotient.mk'' ((g'⁻¹ : M) : M ⧸ H) := by
  refine Quotient.sound' (mem_orbit_iff.mpr ⟨(⟨g'⁻¹ * η⁻¹ * g, hk⟩ : K)⁻¹, ?_⟩)
  show (((⟨g'⁻¹ * η⁻¹ * g, hk⟩ : K)⁻¹ : K) : M) • ((g'⁻¹ : M) : M ⧸ H) = ((g⁻¹ : M) : M ⧸ H)
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
  show ((((g'⁻¹ * η⁻¹ * g)⁻¹ : M) : M) * g'⁻¹)⁻¹ * g⁻¹ ∈ H
  have key : (((g'⁻¹ * η⁻¹ * g)⁻¹ : M) * g'⁻¹)⁻¹ * g⁻¹ = η⁻¹ := by group
  rw [key]
  exact H.inv_mem hη

def toOrbitAux (x : M ⧸ K) : orbitRel.Quotient K (M ⧸ H) :=
  Quotient.liftOn' x (fun g => Quotient.mk'' ((g⁻¹ : M) : M ⧸ H)) fun g g' hgg' => by
    have hk : g'⁻¹ * (1 : M)⁻¹ * g ∈ K := by
      simpa using K.inv_mem (QuotientGroup.leftRel_apply.mp hgg')
    exact mk''_mk_inv_eq H K 1 H.one_mem hk

@[scoped simp]
theorem toOrbitAux_mk (g : M) :
    toOrbitAux H K ((g : M) : M ⧸ K) = Quotient.mk'' ((g⁻¹ : M) : M ⧸ H) :=
  rfl

theorem toOrbitAux_eq_of_mem_orbit {x y : M ⧸ K} (hxy : x ∈ orbit H y) :
    toOrbitAux H K x = toOrbitAux H K y := by
  obtain ⟨η, hη⟩ := hxy
  induction y using QuotientGroup.induction_on with
  | H g' =>
  rw [← hη]
  show toOrbitAux H K (((η : M) * g' : M) : M ⧸ K) = toOrbitAux H K ((g' : M) : M ⧸ K)
  rw [toOrbitAux_mk, toOrbitAux_mk]
  refine mk''_mk_inv_eq H K (η : M) η.2 ?_
  have : g'⁻¹ * (η : M)⁻¹ * ((η : M) * g') = 1 := by group
  rw [this]
  exact K.one_mem

def orbitQuotientEquiv :
    orbitRel.Quotient H (M ⧸ K) ≃ orbitRel.Quotient K (M ⧸ H) where
  toFun q := Quotient.liftOn' q (toOrbitAux H K) fun _ _ h => toOrbitAux_eq_of_mem_orbit H K h
  invFun q := Quotient.liftOn' q (toOrbitAux K H) fun _ _ h => toOrbitAux_eq_of_mem_orbit K H h
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h x =>
      induction x using QuotientGroup.induction_on with
      | H g =>
        show Quotient.mk'' ((g⁻¹⁻¹ : M) : M ⧸ K) = Quotient.mk'' ((g : M) : M ⧸ K)
        rw [inv_inv]
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h x =>
      induction x using QuotientGroup.induction_on with
      | H g =>
        show Quotient.mk'' ((g⁻¹⁻¹ : M) : M ⧸ H) = Quotient.mk'' ((g : M) : M ⧸ H)
        rw [inv_inv]

theorem card_orbitRel_quotient_eq :
    Nat.card (orbitRel.Quotient H (M ⧸ K)) = Nat.card (orbitRel.Quotient K (M ⧸ H)) :=
  Nat.card_congr (orbitQuotientEquiv H K)

noncomputable def quotientEquivOrbitsProd (hKH : ConjTrivial K H) :
    (M ⧸ H) ≃ orbitRel.Quotient K (M ⧸ H) × K := by
  classical
  refine (MulAction.selfEquivSigmaOrbitsQuotientStabilizer K (M ⧸ H)).trans ?_
  refine (Equiv.sigmaCongrRight fun ω => ?_).trans (Equiv.sigmaEquivProd _ _)
  exact (Subgroup.quotientEquivOfEq
    (stabilizer_eq_bot_of_conjTrivial K H hKH ω.out)).trans
    QuotientGroup.quotientBot.toEquiv

theorem card_orbitRelQuotient_mul_card (hKH : ConjTrivial K H) :
    Nat.card (orbitRel.Quotient K (M ⧸ H)) * Nat.card K = H.index := by
  rw [Subgroup.index_eq_card, Nat.card_congr (quotientEquivOrbitsProd H K hKH), Nat.card_prod]

theorem card_orbitRelQuotient_mul_card' (hKH : ConjTrivial K H) :
    Nat.card (orbitRel.Quotient H (M ⧸ K)) * Nat.card K = H.index := by
  rw [card_orbitRel_quotient_eq]
  exact card_orbitRelQuotient_mul_card H K hKH

end DoubleCoset

end FreeDoubleCoset
p2m_reactivate "P2MW.S_Subgroup_card_orbitRelQuotient_mul_card_eq_index.GroupTheory.FreeDoubleCoset"

end GroupTheory
p2m_reactivate "P2MW.S_Subgroup_card_orbitRelQuotient_mul_card_eq_index.GroupTheory.FreeDoubleCoset P2MW.S_Subgroup_card_orbitRelQuotient_mul_card_eq_index.GroupTheory"

theorem solution {M : Type*} [Group M] (H K : Subgroup M)
    (hKH : ∀ g x : M, x ∈ K → g⁻¹ * x * g ∈ H → x = 1) :
    Nat.card (MulAction.orbitRel.Quotient H (M ⧸ K)) * Nat.card K = H.index :=
  GroupTheory.FreeDoubleCoset.card_orbitRelQuotient_mul_card' H K hKH

end S_Subgroup_card_orbitRelQuotient_mul_card_eq_index
end P2MW
export P2MW.S_Subgroup_card_orbitRelQuotient_mul_card_eq_index (solution)
