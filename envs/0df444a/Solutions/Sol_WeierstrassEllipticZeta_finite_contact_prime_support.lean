-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_contact_prime_support
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T01:49:59.610265+00:00
-- url     : https://prove2.me/submissions/4787ee39-78a9-4d0b-a24a-c0dfb753e228

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_ideal_structure
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maximal

noncomputable section
open WeierstrassEllipticZeta

private lemma point_kernel_injective : Function.Injective
    (fun v : Fin 4 → ℂ => RingHom.ker (MvPolynomial.eval v)) := by
  intro v w h
  change RingHom.ker (MvPolynomial.eval v) = RingHom.ker (MvPolynomial.eval w) at h
  funext i
  have hp : MvPolynomial.X i - MvPolynomial.C (v i) ∈
      RingHom.ker (MvPolynomial.eval v) := by simp [RingHom.mem_ker]
  rw [h] at hp
  have hz : w i - v i = 0 := by simpa [RingHom.mem_ker] using hp
  exact (sub_eq_zero.mp hz).symm

theorem solution (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (n : V → ℕ) :
    let I := ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    I.radical = (⨅ v : V, if n v = 0 then ⊤ else RingHom.ker (MvPolynomial.eval v.val)) ∧
    ∀ P : Ideal (MvPolynomial (Fin 4) ℂ), P.IsPrime →
      (I ≤ P ↔ ∃! v : V, 0 < n v ∧ P = RingHom.ker (MvPolynomial.eval v.val)) := by
  classical
  have hc := elliptic_extension_contact_ideal_structure g₂ g₃
  let C : V → Ideal (MvPolynomial (Fin 4) ℂ) := fun v =>
    extensionChartContactIdeal g₂ g₃ c v.val (n v)
  have hzero (v : Fin 4 → ℂ) : extensionChartContactIdeal g₂ g₃ c v 0 = ⊤ := by
    apply top_unique
    intro p _
    exact (hc.1 c v 0 p).mpr (fun k hk => (Nat.not_lt_zero k hk).elim)
  have hrad (v : V) : (C v).radical =
      if n v = 0 then ⊤ else RingHom.ker (MvPolynomial.eval v.val) := by
    by_cases hn : n v = 0
    · simp [C, hn, hzero]
    · simpa only [if_neg hn] using
        (hc.2.2.2.1 c v.val (n v) (Nat.pos_of_ne_zero hn)).1
  have hinf (F : V → Ideal (MvPolynomial (Fin 4) ℂ)) :
      Finset.univ.inf F = ⨅ v : V, F v := by
    simp only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true]
  refine ⟨?_, ?_⟩
  · change (⨅ v : V, C v).radical = _
    rw [← hinf C]
    change Ideal.radicalInfTopHom (Finset.univ.inf C) = _
    rw [map_finset_inf]
    simp only [hinf, Function.comp_apply, Ideal.radicalInfTopHom_apply, hrad]
  · intro P hP
    change (⨅ v : V, C v) ≤ P ↔ _
    constructor
    · intro h
      rw [← hinf C] at h
      obtain ⟨v, _, hv⟩ := hP.inf_le'.mp h
      have hn : 0 < n v := by
        by_contra hn
        have hz : n v = 0 := by omega
        have ht : C v = ⊤ := by simp only [C, hz, hzero]
        exact hP.ne_top (top_unique (ht ▸ hv))
      have hm : (RingHom.ker (MvPolynomial.eval v.val)).IsMaximal :=
        RingHom.ker_isMaximal_of_surjective (MvPolynomial.eval v.val)
          (fun z => ⟨MvPolynomial.C z, MvPolynomial.eval_C z⟩)
      have hradle : RingHom.ker (MvPolynomial.eval v.val) ≤ P := by
        rw [← (hc.2.2.2.1 c v.val (n v) hn).1]
        exact hP.radical_le_iff.mpr hv
      have heq : P = RingHom.ker (MvPolynomial.eval v.val) :=
        (hm.eq_of_le hP.ne_top hradle).symm
      refine ⟨v, ⟨hn, heq⟩, ?_⟩
      intro w hw
      exact Subtype.ext (point_kernel_injective (hw.2.symm.trans heq))
    · rintro ⟨v, hv, _⟩
      rw [hv.2, ← (hc.2.2.2.1 c v.val (n v) hv.1).1]
      exact (iInf_le C v).trans Ideal.le_radical

