-- Prove2me | solution 1 for PI.ET.prod_le_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:27.09963+00:00
-- url     : https://prove2.me/submissions/2d32aaaa-b7ef-41a2-8c53-049313ba5324

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_ProdLeOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.ET
namespace PI.ET
theorem _root_.solution {n k : ℕ} (hk : k ≤ n) (p : Fin n → ℝ) (hp : Antitone p)
    (hpos : ∀ i, 0 ≤ p i) (f : Fin k → Fin n) (hf : Function.Injective f) :
    ∏ i, p (f i) ≤ ∏ i : Fin k, p (Fin.castLE hk i) := by
  classical
  have hs : (Finset.univ.image f).card = k := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  set e := (Finset.univ.image f).orderEmbOfFin hs with he
  have h1 : ∏ i, p (f i) = ∏ j : Fin k, p (e j) := by
    rw [← Finset.prod_image (fun i _ j _ h => hf h), ← Finset.map_orderEmbOfFin_univ _ hs,
      Finset.prod_map]
    rfl
  have h3 : ∀ m (hm : m < k), m ≤ (e ⟨m, hm⟩ : ℕ) := by
    intro m
    induction m with
    | zero => intro _; exact Nat.zero_le _
    | succ m ih =>
      intro hm
      have hlt : e ⟨m, by omega⟩ < e ⟨m + 1, hm⟩ := e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self m))
      have h' : (e ⟨m, by omega⟩ : ℕ) < e ⟨m + 1, hm⟩ := hlt
      have := ih (by omega)
      omega
  rw [h1]
  refine Finset.prod_le_prod (fun j _ => hpos _) fun j _ => hp ?_
  rw [Fin.le_iff_val_le_val, Fin.val_castLE]
  exact h3 j.1 j.2
end PI.ET
