-- Prove2me | solution 1 for PadicInt.exists_isAdicComplete_isMaximal_span_natCast_and_frobenius_sub_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/25231472-9373-5e59-8389-b68c810fb125

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicInt_exists_isAdicComplete_isMaximal_span_natCast_and_frobenius_sub_pow_mem

set_option autoImplicit false

open Polynomial

namespace P2M
namespace WittFrame

variable (q : ℕ) [hq : Fact q.Prime]

abbrev kbar : Type := AlgebraicClosure (ZMod q)

abbrev Onr : Type := WittVector q (kbar q)

noncomputable abbrev ι : ZMod q →+* kbar q := algebraMap (ZMod q) (kbar q)

noncomputable def toOnr : ℤ_[q] →+* Onr q :=
  (WittVector.map (ι q)).comp (WittVector.equiv q).symm.toRingHom

noncomputable scoped instance algebraOnr : Algebra ℤ_[q] (Onr q) := (toOnr q).toAlgebra

theorem algebraMap_eq (z : ℤ_[q]) :
    algebraMap ℤ_[q] (Onr q) z = WittVector.map (ι q) ((WittVector.equiv q).symm z) := rfl

theorem span_algebraMap_eq :
    Ideal.span {algebraMap ℤ_[q] (Onr q) (q : ℤ_[q])} = Ideal.span {(q : Onr q)} := by
  rw [map_natCast]

theorem span_eq_ker :
    Ideal.span {algebraMap ℤ_[q] (Onr q) (q : ℤ_[q])} = RingHom.ker (WittVector.constantCoeff : Onr q →+* kbar q) := by
  rw [span_algebraMap_eq, WittVector.ker_constantCoeff]

theorem mem_span_iff (x : Onr q) :
    x ∈ Ideal.span {algebraMap ℤ_[q] (Onr q) (q : ℤ_[q])} ↔ WittVector.constantCoeff x = 0 := by
  rw [span_eq_ker, RingHom.mem_ker]

theorem frobenius_map (w : WittVector q (ZMod q)) :
    WittVector.frobenius (WittVector.map (ι q) w) = WittVector.map (ι q) w := by
  conv_rhs => rw [← WittVector.frobenius_zmodp (p := q) w]
  ext n
  rw [WittVector.coeff_frobenius_charP, WittVector.map_coeff, WittVector.map_coeff,
    WittVector.coeff_frobenius_charP, map_pow]

theorem frobenius_algebraMap (z : ℤ_[q]) :
    WittVector.frobeniusEquiv q (kbar q) (algebraMap ℤ_[q] (Onr q) z) = algebraMap ℤ_[q] (Onr q) z := by
  rw [algebraMap_eq, WittVector.frobeniusEquiv_apply]
  exact frobenius_map q _

noncomputable def Fr : Onr q ≃ₐ[ℤ_[q]] Onr q :=
  AlgEquiv.ofRingEquiv (f := WittVector.frobeniusEquiv q (kbar q)) (frobenius_algebraMap q)

theorem Fr_apply (x : Onr q) : Fr q x = WittVector.frobenius x := rfl

theorem Fr_sub_pow_mem (x : Onr q) : Fr q x - x ^ q ∈ Ideal.span {algebraMap ℤ_[q] (Onr q) (q : ℤ_[q])} := by
  rw [mem_span_iff, map_sub, map_pow, Fr_apply, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
    WittVector.coeff_frobenius_charP, sub_self]

theorem charZero : CharZero (Onr q) := by
  have hqP : q.Prime := hq.out
  refine charZero_of_inj_zero (fun n hn => ?_)
  by_contra h0
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 q hqP.one_lt.ne'
  have hm0 : ((m : ℕ) : kbar q) ≠ 0 := fun h => hm ((CharP.cast_eq_zero_iff (kbar q) q m).mp h)
  have hmU : IsUnit ((m : ℕ) : Onr q) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [← WittVector.constantCoeff_apply, map_natCast]
    exact hm0
  have hqe : ((q : Onr q)) ^ e ≠ 0 := pow_ne_zero _ (WittVector.irreducible q).ne_zero
  rw [Nat.cast_mul, Nat.cast_pow] at hn
  exact (mul_ne_zero hqe hmU.ne_zero) hn

theorem isMaximal : (Ideal.span {algebraMap ℤ_[q] (Onr q) (q : ℤ_[q])}).IsMaximal := by
  rw [span_eq_ker]
  exact RingHom.ker_isMaximal_of_surjective _
    (fun r => ⟨WittVector.teichmuller q r, WittVector.teichmuller_coeff_zero q r⟩)

theorem ringHom_eq_toZMod (ψ : ℤ_[q] →+* ZMod q) (z : ℤ_[q]) : ψ z = PadicInt.toZMod z := by
  have hz := PadicInt.toZMod_spec z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hz
  obtain ⟨y, hy⟩ := hz
  have h1 : ψ (z - (ZMod.cast (PadicInt.toZMod z) : ℤ_[q])) = 0 := by
    rw [hy, map_mul, map_natCast, ZMod.natCast_self, zero_mul]
  rw [map_sub, sub_eq_zero] at h1
  rw [h1, ZMod.cast_eq_val, map_natCast, ZMod.natCast_zmod_val]

theorem constantCoeff_comp_algebraMap :
    (WittVector.constantCoeff : Onr q →+* kbar q).comp (algebraMap ℤ_[q] (Onr q)) =
      (ι q).comp (PadicInt.toZMod : ℤ_[q] →+* ZMod q) := by
  ext z
  rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_eq, WittVector.constantCoeff_apply, WittVector.map_coeff,
    ← WittVector.constantCoeff_apply,
    ← ringHom_eq_toZMod q (WittVector.constantCoeff.comp (WittVector.equiv q).symm.toRingHom) z]
  rfl

theorem residue_algebraic (x : Onr q) :
    ∃ p : Polynomial ℤ_[q], p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap ℤ_[q] (Onr q) (q : ℤ_[q])} := by
  set x₀ : kbar q := WittVector.constantCoeff x with hx₀
  have hint : IsIntegral (ZMod q) x₀ := (Algebra.IsAlgebraic.isAlgebraic x₀).isIntegral
  have hsurj : Function.Surjective (PadicInt.toZMod : ℤ_[q] →+* ZMod q) := ZMod.ringHom_surjective _
  obtain ⟨F, hFmap, -, hFmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic (Polynomial.mem_lifts_of_surjective hsurj (minpoly (ZMod q) x₀))
      (minpoly.monic hint)
  refine ⟨F, hFmonic, ?_⟩
  rw [mem_span_iff, Polynomial.aeval_def, Polynomial.hom_eval₂, constantCoeff_comp_algebraMap, ← Polynomial.eval₂_map,
    hFmap, ← hx₀]
  exact minpoly.aeval (ZMod q) x₀

theorem residue_algClosed (p : Polynomial (Onr q)) (hp : p.Monic) (hdeg : 0 < p.natDegree) :
    ∃ x : Onr q, Polynomial.eval x p ∈ Ideal.span {algebraMap ℤ_[q] (Onr q) (q : ℤ_[q])} := by
  set pbar : Polynomial (kbar q) := p.map WittVector.constantCoeff with hpbar
  have hmon : pbar.Monic := hp.map _
  have hnat : pbar.natDegree = p.natDegree := hp.natDegree_map _
  have hdeg' : pbar.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hmon.ne_zero, hnat]
    exact_mod_cast hdeg.ne'
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root pbar hdeg'
  refine ⟨WittVector.teichmuller q r, ?_⟩
  rw [mem_span_iff]
  have : WittVector.constantCoeff (Polynomial.eval (WittVector.teichmuller q r) p) =
      Polynomial.eval r pbar := by
    rw [hpbar, Polynomial.eval_map, ← Polynomial.eval₂_id (R := Onr q), Polynomial.hom_eval₂, RingHom.comp_id,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  rw [this]
  exact hr

end P2M.WittFrame
p2m_reactivate "P2MW.S_PadicInt_exists_isAdicComplete_isMaximal_span_natCast_and_frobenius_sub_pow_mem.P2M P2MW.S_PadicInt_exists_isAdicComplete_isMaximal_span_natCast_and_frobenius_sub_pow_mem.P2M.WittFrame"
p2m_reactivate "P2MW.S_PadicInt_exists_isAdicComplete_isMaximal_span_natCast_and_frobenius_sub_pow_mem.P2M"

open P2M.WittFrame in
theorem solution
    (q : ℕ) [Fact q.Prime] :
    ∃ (Onr : Type) (_ : CommRing Onr) (_ : IsDomain Onr) (_ : IsDiscreteValuationRing Onr) (_ : CharZero Onr)
      (_ : Algebra ℤ_[q] Onr) (Fr : Onr ≃ₐ[ℤ_[q]] Onr),
      IsAdicComplete (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) Onr ∧
      (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal ∧
      (∀ x : Onr, ∃ p : Polynomial ℤ_[q], p.Monic ∧
        Polynomial.aeval x p ∈ Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) ∧
      (∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree →
        ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) ∧
      (∀ x : Onr, Fr x - x ^ q ∈ Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) := by
  refine ⟨Onr q, inferInstance, inferInstance, inferInstance, charZero q, inferInstance, Fr q, ?_, isMaximal q,
    residue_algebraic q, residue_algClosed q, Fr_sub_pow_mem q⟩
  rw [span_algebraMap_eq]
  infer_instance

end S_PadicInt_exists_isAdicComplete_isMaximal_span_natCast_and_frobenius_sub_pow_mem
end P2MW
export P2MW.S_PadicInt_exists_isAdicComplete_isMaximal_span_natCast_and_frobenius_sub_pow_mem (solution)
