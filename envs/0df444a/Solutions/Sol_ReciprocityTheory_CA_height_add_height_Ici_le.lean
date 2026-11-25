-- Prove2me | solution 1 for ReciprocityTheory.CA.height_add_height_Ici_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:08:32.914977+00:00
-- url     : https://prove2.me/submissions/40fb4b11-57ee-4309-ab74-058ddde2fdef

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_IsSaturatedChain
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing
namespace ReciprocityTheory.CA
theorem _root_.solution {α : Type*} [PartialOrder α] {a b : α} (hab : a ≤ b) :
    Order.height a + Order.height (⟨b, hab⟩ : Set.Ici a) ≤ Order.height b := by
  rcases eq_or_ne (Order.height b) ⊤ with hb | hb
  · rw [hb]; exact le_top
  have hmono : StrictMono (Subtype.val : Set.Ici a → α) := fun _ _ h => h
  have h1 : Order.height a ≠ ⊤ := ne_top_of_le_ne_top hb (Order.height_mono hab)
  have h2 : Order.height (⟨b, hab⟩ : Set.Ici a) ≠ ⊤ :=
    ne_top_of_le_ne_top hb (Order.height_le_height_apply_of_strictMono _ hmono ⟨b, hab⟩)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h1
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h2
  obtain ⟨s, hsl, hsn⟩ := Order.exists_series_of_le_height a (n := n) hn.le
  obtain ⟨t, htl, htm⟩ := Order.exists_series_of_le_height (⟨b, hab⟩ : Set.Ici a) (n := m) hm.le
  rw [← hn, ← hm]
  let t' : LTSeries α := t.map Subtype.val hmono
  have ht'l : t'.last = b := by
    show ((t.last : Set.Ici a) : α) = b
    rw [htl]
  have ht'len : t'.length = m := htm
  have hhead : a ≤ t'.head := t.head.2
  rcases hhead.eq_or_lt with he | hlt
  ·
    have hc : s.last = t'.head := hsl.trans he
    have hlen : (s.smash t' hc).length = n + m := by
      show s.length + t'.length = n + m
      rw [hsn, ht'len]
    have hlast : (s.smash t' hc).last = b := by
      first
      | (rw [RelSeries.last_smash]; exact ht'l)
      | (rw [RelSeries.smash_last]; exact ht'l)
      | simp [ht'l]
    calc ((n : ℕ∞) + (m : ℕ∞)) = ((s.smash t' hc).length : ℕ∞) := by rw [hlen]; norm_cast
      _ ≤ Order.height b := Order.length_le_height hlast.le
  ·
    have hc : s.last < t'.head := by rw [hsl]; exact hlt
    have hlen : (s.append t' hc).length = n + m + 1 := by
      show s.length + t'.length + 1 = n + m + 1
      rw [hsn, ht'len]
    have hlast : (s.append t' hc).last = b := by
      first
      | (rw [RelSeries.last_append]; exact ht'l)
      | (rw [RelSeries.append_last]; exact ht'l)
      | simp [ht'l]
    calc ((n : ℕ∞) + (m : ℕ∞)) ≤ ((n + m + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ (n + m)
      _ = ((s.append t' hc).length : ℕ∞) := by rw [hlen]
      _ ≤ Order.height b := Order.length_le_height hlast.le
end ReciprocityTheory.CA
