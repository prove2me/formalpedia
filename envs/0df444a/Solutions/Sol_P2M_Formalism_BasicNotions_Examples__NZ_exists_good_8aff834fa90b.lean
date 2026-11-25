-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_exists_good_8aff834fa90b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:12:57.527746+00:00
-- url     : https://prove2.me/submissions/b2d9026d-3f27-4e08-bcc1-3906dab2e1ed

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeC
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_exists_labels_77c94fa8b886
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (N p q0 : ℕ) (hp : p.Prime) (h1 : N < 2 * p) (h2 : p + 3 ≤ N) (hq0 : q0.Prime)
    (hq2 : q0 ≠ 2) (h2g : 2 ∣ g - 1) (hqg : q0 ∣ g - 1) :
    ∃ fA fB : (ZMod g)[X], fA ≠ fB ∧ (fA.Monic ∧ fA.natDegree = N ∧ fA.coeff 0 ≠ 0) ∧
      (fB.Monic ∧ fB.natDegree = N ∧ fB.coeff 0 ≠ 0) ∧
      ∀ (PP J : Type) (t : PP → Bool), (∃ v, t v = true) → (∃ v, t v = false) →
        IsGood N g (fun v => if t v then fA else fB) (fun (_ : PP) (_ : J) => (1 : (ZMod g)ˣ)) := by
  obtain ⟨fA, fB, q, hA, hB, hdiv, hq, hqB, hqd⟩ := exists_labels (g := g) N p q0 hp h1 h2 hq0 hq2 h2g hqg
  refine ⟨fA, fB, fun e => ?_, ⟨hA.monic, hA.deg, hA.c0⟩, ⟨hB.monic, hB.deg, hB.c0⟩,
    fun PP J t ⟨vA, hvA⟩ ⟨vB, hvB⟩ => ?_⟩
  · have := hdiv q (e ▸ hqB) (by rw [hqd]; exact hp.ne_zero)
    omega
  have hOK : ∀ v, LabelOK N (if t v then fA else fB) := fun v => by split_ifs <;> assumption
  refine ⟨fun v => ⟨(hOK v).monic, (hOK v).deg, (hOK v).c0⟩, fun v => (hOK v).sqf,
    fun ℓ hℓ hBB v => (hOK v).inj ℓ hℓ hBB, fun ℓ hℓ _ v _ x hx => ?_, fun a ha1 ha2 => ⟨vA, ?_⟩,
    ⟨vB, q, hq, ?_, hqd ▸ hp, by omega, by omega⟩⟩
  · rw [Units.val_one, map_one]; exact (hOK v).ne1 ℓ hℓ x hx
  · rintro ⟨r, hr, hra⟩
    simp only [hvA, if_true] at hr
    have := hdiv r hr (by omega)
    omega
  · simp only [hvB]; exact hqB
end Formalism.BasicNotions.Examples₂.NZ
