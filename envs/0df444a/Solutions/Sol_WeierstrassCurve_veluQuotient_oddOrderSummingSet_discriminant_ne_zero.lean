-- Prove2me | solution 1 for WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8e008aec-90e8-5c2d-8f8e-e9c0a48d278c

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Theorems.Thm_WeierstrassCurve_veluX_oddOrderSummingSet_injOn_psi2Sq_roots
import Theorems.Thm_WeierstrassCurve_eval_psi2Sq_veluQuotient_veluX_eq_zero_of_eval_psi2Sq_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty"

set_option autoImplicit false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero.WeierstrassCurve"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "twoTorsionPolynomial_discr map twoTorsionPolynomial Ψ₂Sq map_id toAffine Δ Δ' veluQuotient oddOrderSummingSet veluX veluX_oddOrderSummingSet_injOn_psi2Sq_roots eval_psi2Sq_veluQuotient_veluX_eq_zero_of_eval_psi2Sq_eq_zero"
p2m_open "WeierstrassCurve"

variable {L : Type*} [Field L] (V : WeierstrassCurve L)

private lemma _root_.WeierstrassCurve.ws18_Ψ₂Sq_eq_toPoly : V.Ψ₂Sq = V.twoTorsionPolynomial.toPoly := by
  simp only [Ψ₂Sq, twoTorsionPolynomial, Cubic.toPoly]

p2m_export "WeierstrassCurve" "ws18_Ψ₂Sq_eq_toPoly"
private lemma _root_.WeierstrassCurve.ws18_Ψ₂Sq_ne_zero (h4 : (4 : L) ≠ 0) : V.Ψ₂Sq ≠ 0 := by
  rw [ws18_Ψ₂Sq_eq_toPoly]
  exact Cubic.ne_zero_of_a_ne_zero h4

p2m_export "WeierstrassCurve" "ws18_Ψ₂Sq_ne_zero"
end WeierstrassCurve

theorem solution
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] (h2 : (2 : L) ≠ 0)
    (W : WeierstrassCurve L) [W.IsElliptic] (n : ℕ) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0 := by
  set S := W.oddOrderSummingSet Q n with hSdef
  set V' := W.veluQuotient S with hV'def
  have h4 : (4 : L) ≠ 0 := by
    have : (4 : L) = (2 : L) ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero 2 h2
  have h16 : (16 : L) ≠ 0 := by
    have : (16 : L) = (2 : L) ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero 4 h2

  have haV : W.twoTorsionPolynomial.a ≠ 0 := h4
  have hdiscrV : W.twoTorsionPolynomial.discr ≠ 0 := by
    rw [twoTorsionPolynomial_discr]; exact mul_ne_zero h16 W.Δ'.ne_zero
  have hsplitV : (W.twoTorsionPolynomial.toPoly.map (RingHom.id L)).Splits :=
    IsAlgClosed.splits _
  obtain ⟨r₁, r₂, r₃, hroots⟩ := (Cubic.splits_iff_roots_eq_three haV).mp hsplitV
  obtain ⟨hne₁₂, hne₁₃, hne₂₃⟩ := (Cubic.discr_ne_zero_iff_roots_ne haV hroots).mp hdiscrV
  have hrootsΨ : W.Ψ₂Sq.roots = {r₁, r₂, r₃} := by
    rwa [Cubic.map_roots, Polynomial.map_id, ← W.ws18_Ψ₂Sq_eq_toPoly] at hroots
  have hev : ∀ r ∈ ({r₁, r₂, r₃} : Multiset L), W.Ψ₂Sq.eval r = 0 := fun r hr =>
    ((Polynomial.mem_roots').mp (hrootsΨ ▸ hr)).2
  have hev₁ : W.Ψ₂Sq.eval r₁ = 0 := hev r₁ (by simp)
  have hev₂ : W.Ψ₂Sq.eval r₂ = 0 := hev r₂ (by simp)
  have hev₃ : W.Ψ₂Sq.eval r₃ = 0 := hev r₃ (by simp)

  have him₁ := W.eval_psi2Sq_veluQuotient_veluX_eq_zero_of_eval_psi2Sq_eq_zero h2 n Q hQ hev₁
  have him₂ := W.eval_psi2Sq_veluQuotient_veluX_eq_zero_of_eval_psi2Sq_eq_zero h2 n Q hQ hev₂
  have him₃ := W.eval_psi2Sq_veluQuotient_veluX_eq_zero_of_eval_psi2Sq_eq_zero h2 n Q hQ hev₃

  have him_ne₁₂ : W.veluX S r₁ ≠ W.veluX S r₂ := fun h =>
    hne₁₂ (W.veluX_oddOrderSummingSet_injOn_psi2Sq_roots h2 n Q hQ hev₁ hev₂ h)
  have him_ne₁₃ : W.veluX S r₁ ≠ W.veluX S r₃ := fun h =>
    hne₁₃ (W.veluX_oddOrderSummingSet_injOn_psi2Sq_roots h2 n Q hQ hev₁ hev₃ h)
  have him_ne₂₃ : W.veluX S r₂ ≠ W.veluX S r₃ := fun h =>
    hne₂₃ (W.veluX_oddOrderSummingSet_injOn_psi2Sq_roots h2 n Q hQ hev₂ hev₃ h)

  have ha' : V'.twoTorsionPolynomial.a ≠ 0 := h4
  have hΨ₂'ne : V'.Ψ₂Sq ≠ 0 := V'.ws18_Ψ₂Sq_ne_zero h4
  have hdeg' : V'.Ψ₂Sq.natDegree = 3 := by
    rw [V'.ws18_Ψ₂Sq_eq_toPoly]; exact Cubic.natDegree_of_a_ne_zero ha'
  have hsubnodup : ({W.veluX S r₁, W.veluX S r₂, W.veluX S r₃} : Multiset L).Nodup := by
    refine Multiset.nodup_cons.mpr ⟨?_,
      Multiset.nodup_cons.mpr ⟨by simpa using him_ne₂₃, Multiset.nodup_singleton _⟩⟩
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
    exact not_or.mpr ⟨him_ne₁₂, him_ne₁₃⟩
  have hsub : ({W.veluX S r₁, W.veluX S r₂, W.veluX S r₃} : Multiset L) ≤ V'.Ψ₂Sq.roots := by
    refine (Multiset.le_iff_subset hsubnodup).mpr ?_
    intro a ha
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact (Polynomial.mem_roots hΨ₂'ne).mpr him₁
    · exact (Polynomial.mem_roots hΨ₂'ne).mpr him₂
    · exact (Polynomial.mem_roots hΨ₂'ne).mpr him₃
  have hrootsV' : V'.Ψ₂Sq.roots = {W.veluX S r₁, W.veluX S r₂, W.veluX S r₃} := by
    refine (Multiset.eq_of_le_of_card_le hsub ?_).symm
    rw [show Multiset.card ({W.veluX S r₁, W.veluX S r₂, W.veluX S r₃} : Multiset L) = 3 from by
      simp]
    exact hdeg' ▸ Polynomial.card_roots' V'.Ψ₂Sq
  have hrootsV'Cubic : (Cubic.map (RingHom.id L) V'.twoTorsionPolynomial).roots
      = {W.veluX S r₁, W.veluX S r₂, W.veluX S r₃} := by
    rw [Cubic.map_roots, Polynomial.map_id, ← V'.ws18_Ψ₂Sq_eq_toPoly]; exact hrootsV'
  have hdiscr' : V'.twoTorsionPolynomial.discr ≠ 0 :=
    (Cubic.discr_ne_zero_iff_roots_ne ha' hrootsV'Cubic).mpr ⟨him_ne₁₂, him_ne₁₃, him_ne₂₃⟩
  intro hΔ'
  exact hdiscr' (by rw [twoTorsionPolynomial_discr, hΔ', mul_zero])

end S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero (solution)
