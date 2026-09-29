-- Prove2me | solution 1 for ValuationSubring.exists_forall_mem_and_forall_isUnit_polynomialEval2_of_finset_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/2ef6b606-56c0-5345-9cb8-6cf367c250a8

import Mathlib
import Theorems.Thm_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_forall_mem_and_forall_isUnit_polynomialEval2_of_finset_of_isDiscreteValuationRing

set_option autoImplicit false

open IsLocalRing

namespace CommonElt

variable {F₀ : Type} [Field F₀]

theorem exists_not_mem_of_dvr (O : ValuationSubring F₀) (hO : IsDiscreteValuationRing ↥O) :
    ∃ y : F₀, y ∉ O := by
  haveI := hO
  have hne : maximalIdeal ↥O ≠ ⊥ := IsDiscreteValuationRing.not_a_field ↥O
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hmn : (m : F₀) ∈ O.nonunits := ValuationSubring.coe_mem_nonunits_iff.mpr hm
  have hm0' : (m : F₀) ≠ 0 := fun h => hm0 (Subtype.ext h)
  rcases (ValuationSubring.mem_nonunits_iff_or (A := O)).mp hmn with h | h
  · exact absurd h hm0'
  · exact ⟨_, h⟩

theorem eq_of_le_of_dvr (O O' : ValuationSubring F₀) (h : O ≤ O')
    (hO : IsDiscreteValuationRing ↥O) (hO' : IsDiscreteValuationRing ↥O') : O = O' := by
  haveI := hO
  refine le_antisymm h (ValuationSubring.nonunits_le_nonunits.mp ?_)

  let P : Ideal ↥O := (maximalIdeal ↥O').comap (ValuationSubring.inclusion O O' h)
  haveI hP : P.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨y, hy⟩ := exists_not_mem_of_dvr O' hO'
  have hyO : y ∉ O := fun hy' => hy (h hy')
  have hyinv : y⁻¹ ∈ O := (O.mem_or_inv_mem y).resolve_left hyO
  have hyinv' : y⁻¹ ∈ O'.nonunits := (ValuationSubring.inv_mem_nonunits_iff (A := O')).mpr (Or.inr hy)
  have hy0 : y ≠ 0 := fun h0 => hyO (h0.symm ▸ O.zero_mem)
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hmem : (⟨y⁻¹, hyinv⟩ : ↥O) ∈ P := by
      show ValuationSubring.inclusion O O' h ⟨y⁻¹, hyinv⟩ ∈ maximalIdeal ↥O'
      exact ValuationSubring.coe_mem_nonunits_iff.mp hyinv'
    rw [hbot, Ideal.mem_bot] at hmem
    exact inv_ne_zero hy0 (congrArg Subtype.val hmem)
  have hPmax : P = maximalIdeal ↥O := IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal (S := P) hPne)
  intro x hx
  obtain ⟨hxO, hxm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hx
  rw [← hPmax] at hxm
  exact ValuationSubring.coe_mem_nonunits_iff.mpr (Ideal.mem_comap.mp hxm)

variable {A₀ : Type} [CommRing A₀] (j₀ : A₀ →+* F₀)

def Geometric (O : ValuationSubring F₀) (f : F₀) : Prop :=
  f ∈ O ∧ ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) →
    ∃ hO : Polynomial.eval₂ j₀ f p ∈ O, IsUnit (⟨_, hO⟩ : ↥O)

theorem map_mem_of_geometric {O : ValuationSubring F₀} {f : F₀} (hf : Geometric j₀ O f) (a : A₀) : j₀ a ∈ O := by
  obtain ⟨hfO, hgeo⟩ := hf
  obtain ⟨hO, -⟩ := hgeo (Polynomial.X + Polynomial.C a) ⟨1, by simp⟩
  have : Polynomial.eval₂ j₀ f (Polynomial.X + Polynomial.C a) = f + j₀ a := by
    simp [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C]
  rw [this] at hO
  have := O.sub_mem hO hfO
  rwa [add_sub_cancel_left] at this

theorem geometric_of_sub_mem_nonunits {O : ValuationSubring F₀} {f z : F₀} (hf : Geometric j₀ O f)
    (hz : z ∈ O) (hzf : z - f ∈ O.nonunits) : Geometric j₀ O z := by
  have hA : ∀ a, j₀ a ∈ O := map_mem_of_geometric j₀ hf
  obtain ⟨hfO, hgeo⟩ := hf

  let j' : A₀ →+* ↥O := j₀.codRestrict O.toSubring hA
  have hj' : ∀ (x : F₀) (hx : x ∈ O) (p : Polynomial A₀),
      ((Polynomial.eval₂ j' (⟨x, hx⟩ : ↥O) p : ↥O) : F₀) = Polynomial.eval₂ j₀ x p := by
    intro x hx p
    rw [show ((Polynomial.eval₂ j' (⟨x, hx⟩ : ↥O) p : ↥O) : F₀) = O.subtype (Polynomial.eval₂ j' ⟨x, hx⟩ p) from rfl,
      Polynomial.hom_eval₂]
    rfl
  refine ⟨hz, fun p hp => ?_⟩
  obtain ⟨hO, hu⟩ := hgeo p hp
  have hmemz : Polynomial.eval₂ j₀ z p ∈ O := by
    rw [← hj' z hz p]; exact Subtype.coe_prop _
  refine ⟨hmemz, ?_⟩

  have hzf' : (⟨z, hz⟩ : ↥O) - ⟨f, hfO⟩ ∈ maximalIdeal ↥O :=
    ValuationSubring.coe_mem_nonunits_iff.mp (by simpa using hzf)
  have hdvd := Polynomial.sub_dvd_eval_sub (⟨z, hz⟩ : ↥O) ⟨f, hfO⟩ (p.map j')
  rw [← Polynomial.eval₂_eq_eval_map, ← Polynomial.eval₂_eq_eval_map] at hdvd
  have hdiff : Polynomial.eval₂ j' (⟨z, hz⟩ : ↥O) p - Polynomial.eval₂ j' ⟨f, hfO⟩ p ∈ maximalIdeal ↥O :=
    Ideal.mem_of_dvd _ hdvd hzf'
  have hfu : IsUnit (Polynomial.eval₂ j' (⟨f, hfO⟩ : ↥O) p) := by
    have : Polynomial.eval₂ j' (⟨f, hfO⟩ : ↥O) p = ⟨_, hO⟩ := Subtype.ext (hj' f hfO p)
    rw [this]; exact hu
  have hzu : IsUnit (Polynomial.eval₂ j' (⟨z, hz⟩ : ↥O) p) := by
    by_contra hnu
    have hmem : Polynomial.eval₂ j' (⟨z, hz⟩ : ↥O) p ∈ maximalIdeal ↥O := (mem_maximalIdeal _).mpr hnu
    have := Ideal.sub_mem _ hmem hdiff
    rw [sub_sub_cancel] at this
    exact (mem_maximalIdeal _).mp this hfu
  have : (⟨_, hmemz⟩ : ↥O) = Polynomial.eval₂ j' (⟨z, hz⟩ : ↥O) p := Subtype.ext (hj' z hz p).symm
  rw [this]; exact hzu

end CommonElt

open CommonElt in
theorem solution
    {A₀ : Type} [CommRing A₀] {F₀ : Type} [Field F₀] (j₀ : A₀ →+* F₀)
    (V : Finset (ValuationSubring F₀))
    (hdvr : ∀ O ∈ V, IsDiscreteValuationRing ↥O)
    (hgeo : ∀ O ∈ V, ∃ f : F₀, f ∈ O ∧ ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) →
      ∃ hO : Polynomial.eval₂ j₀ f p ∈ O, IsUnit (⟨_, hO⟩ : ↥O)) :
    ∃ f : F₀, ∀ O ∈ V, f ∈ O ∧ ∀ p : Polynomial A₀, (∃ i, IsUnit (p.coeff i)) →
      ∃ hO : Polynomial.eval₂ j₀ f p ∈ O, IsUnit (⟨_, hO⟩ : ↥O) := by
  classical

  have hinc : ∀ i j : ↥V, (i : ValuationSubring F₀) ≤ j → i = j := fun i j h =>
    Subtype.ext (eq_of_le_of_dvr _ _ h (hdvr _ i.2) (hdvr _ j.2))
  choose f hf using hgeo
  obtain ⟨z, hz⟩ := ValuationSubring.exists_forall_mem_and_sub_mem_nonunits
    (fun i : ↥V => (i : ValuationSubring F₀)) hinc (fun i => f i.1 i.2) (fun i => (hf i.1 i.2).1)
  refine ⟨z, fun O hO => ?_⟩
  obtain ⟨hzO, hzf⟩ := hz ⟨O, hO⟩
  exact geometric_of_sub_mem_nonunits j₀ (hf O hO) hzO hzf

end S_ValuationSubring_exists_forall_mem_and_forall_isUnit_polynomialEval2_of_finset_of_isDiscreteValuationRing
end P2MW
export P2MW.S_ValuationSubring_exists_forall_mem_and_forall_isUnit_polynomialEval2_of_finset_of_isDiscreteValuationRing (solution)
