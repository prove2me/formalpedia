-- Prove2me | solution 1 for PaleyWeil.mem_minpoly_image_iff
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T17:30:33.470903+00:00
-- url     : https://prove2.me/submissions/bef4e430-e841-4b94-bed5-71bfaa09f6fc

import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial


open Polynomial Finset
open PaleyWeil

theorem solution {K L : Type*} [Field K] [Field L]
    [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L] [Algebra K L] (P : K[X]) :
    P ∈ (Finset.univ.image (minpoly K : L → K[X])) ↔
      P.Monic ∧ Irreducible P ∧ P.natDegree ∣ Module.finrank K L := by
  classical
  constructor
  · rintro h
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
    have hx : IsIntegral K x := IsIntegral.of_finite K x
    exact ⟨minpoly.monic hx, minpoly.irreducible hx, minpoly.degree_dvd hx⟩
  · rintro ⟨hmonic, hirr, hdiv⟩
    have hcard : Nat.card K ^ Module.finrank K L = Fintype.card L := by
      rw [Nat.card_eq_fintype_card]
      exact (Module.card_eq_pow_finrank (K := K) (V := L)).symm
    have hPdvd : P ∣ (X ^ Nat.card K ^ Module.finrank K L - X : K[X]) :=
      hirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp hdiv
    let g : L[X] := X ^ Fintype.card L - X
    have hg0 : g ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L Fintype.one_lt_card
    have hgdeg : g.natDegree = Fintype.card L :=
      FiniteField.X_pow_card_sub_X_natDegree_eq L Fintype.one_lt_card
    have hgroots : g.roots = (Finset.univ : Finset L).val :=
      FiniteField.roots_X_pow_card_sub_X L
    have hgsplits : g.Splits := by
      rw [splits_iff_card_roots, hgroots, hgdeg]
      exact Finset.card_univ
    have hmap : P.map (algebraMap K L) ∣ g := by
      have h := Polynomial.map_dvd (algebraMap K L) hPdvd
      simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, hcard] using h
    have hsplits : (P.map (algebraMap K L)).Splits := hgsplits.of_dvd hg0 hmap
    obtain ⟨x, hx⟩ := hsplits.exists_eval_eq_zero (degree_ne_of_natDegree_ne (by
      rw [natDegree_map]
      exact hirr.natDegree_pos.ne'))
    have hroot : aeval x P = 0 := by
      simpa only [eval_map, aeval_def] using hx
    refine Finset.mem_image.mpr ⟨x, Finset.mem_univ x, ?_⟩
    exact (minpoly.eq_of_irreducible_of_monic hirr hroot hmonic).symm
