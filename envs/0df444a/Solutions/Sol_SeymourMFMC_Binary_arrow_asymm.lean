-- Prove2me | solution 1 for SeymourMFMC.Binary.arrow_asymm
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:58:27.721614+00:00
-- url     : https://prove2.me/submissions/950fb402-08e9-4630-8daf-e98eabadec7a

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Linarith
import Definitions.Def_SeymourMFMC_Binary_ground
import Definitions.Def_SeymourMFMC_Binary_IsClutter
import Definitions.Def_SeymourMFMC_Binary_IsBinary
import Definitions.Def_SeymourMFMC_Binary_IsMengerian
import Definitions.Def_SeymourMFMC_Binary_IsCritical
import Definitions.Def_SeymourMFMC_Binary_Arrow
import Theorems.Thm_SeymourMFMC_Binary_arrow_circuit

namespace SeymourMFMC.Binary

/-- Seymour 1977, (4.3), p. 206: if `L` is a critical Mengerian binary clutter, `x, y ∈ E(L)`
and `x → y`, then `y ↛ x`. -/
theorem arrow_asymm {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) (hM : IsMengerian L) (hcrit : IsCritical L)
    (x y : α) (_hx : x ∈ ground L) (_hy : y ∈ ground L) (hxy : Arrow L x y) :
    ¬ Arrow L y x := by
  intro hyx
  obtain ⟨C, _, hxC, hyC, hcard3, hC_arr, hC_tau⟩ :=
    arrow_circuit L hL hbin hM hcrit x y hxy
  have hxy_ne : x ≠ y := fun h => hxy.2.2.2 (h ▸ Finset.mem_insert_self x _)
  have hx_er : x ∈ C.erase y := Finset.mem_erase.mpr ⟨hxy_ne, hxC⟩
  have hcard_er1 : (C.erase y).card + 1 = C.card := Finset.card_erase_add_one hyC
  have hcard_er2 : ((C.erase y).erase x).card + 1 = (C.erase y).card :=
    Finset.card_erase_add_one hx_er
  obtain ⟨z, hz_er2⟩ : ((C.erase y).erase x).Nonempty := Finset.card_pos.mp (by omega)
  have hzx : z ≠ x := (Finset.mem_erase.mp hz_er2).1
  have hz_er : z ∈ C.erase y := (Finset.mem_erase.mp hz_er2).2
  have hzy : Arrow L z y := hC_arr z hz_er
  have hz_mb : z ∈ ground (mb L) := hcrit.symm ▸ hzy.1
  rw [ground, Finset.mem_sup] at hz_mb
  rcases hz_mb with ⟨B, hB_mb, hzB⟩
  have hyB : y ∈ B := hzy.2.2.1 B hB_mb hzB
  have hxB : x ∈ B := hyx.2.2.1 B hB_mb hyB
  have hB_bl : B ∈ blocker L := (Finset.mem_filter.mp hB_mb).1
  have hB_card : B.card = tau L := (Finset.mem_filter.mp hB_mb).2
  have htau := hC_tau B hB_bl
  have hsum := Finset.card_sdiff_add_card_inter B (C.erase y)
  have hle1 : (B ∩ C.erase y).card ≤ 1 := by omega
  have hz_inter : z ∈ B ∩ C.erase y := Finset.mem_inter.mpr ⟨hzB, hz_er⟩
  have hx_inter : x ∈ B ∩ C.erase y := Finset.mem_inter.mpr ⟨hxB, hx_er⟩
  exact hzx (Finset.card_le_one.mp hle1 z hz_inter x hx_inter)

end SeymourMFMC.Binary

theorem solution {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : SeymourMFMC.Binary.IsClutter L) (hbin : SeymourMFMC.Binary.IsBinary L)
    (hM : SeymourMFMC.Binary.IsMengerian L) (hcrit : SeymourMFMC.Binary.IsCritical L)
    (x y : α) (hx : x ∈ SeymourMFMC.Binary.ground L) (hy : y ∈ SeymourMFMC.Binary.ground L)
    (hxy : SeymourMFMC.Binary.Arrow L x y) :
    ¬ SeymourMFMC.Binary.Arrow L y x :=
  SeymourMFMC.Binary.arrow_asymm L hL hbin hM hcrit x y hx hy hxy
