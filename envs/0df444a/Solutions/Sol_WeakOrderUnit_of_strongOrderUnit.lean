-- Prove2me | solution 1 for WeakOrderUnit.of_strongOrderUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:19:08.030743+00:00
-- url     : https://prove2.me/submissions/3e3b90e2-2cef-4cb2-97b4-9710cdc7a9e0

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Theorems.Thm_abs_eq_zero_iff_zero
public import Theorems.Thm_inf_le_inf_add_inf_of_nonneg

section
@[expose] public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
private lemma abs_inf_natCast_smul_eq_zero {x e : X} (he : 0 ≤ e)
    (hxe : |x| ⊓ e = 0) : ∀ k : ℕ, |x| ⊓ ((k : ℝ) • e) = 0
  | 0 => by simp
  | k + 1 => by
      have ih := abs_inf_natCast_smul_eq_zero he hxe k
      have hke : 0 ≤ ((k : ℝ) • e) :=
        smul_nonneg (Nat.cast_nonneg k) he
      have hsucc : ((k + 1 : ℕ) : ℝ) • e = (k : ℝ) • e + e := by
        push_cast; rw [add_smul, one_smul]
      rw [hsucc]
      refine le_antisymm ?_
        (le_inf (abs_nonneg _) (add_nonneg hke he))
      calc |x| ⊓ ((k : ℝ) • e + e)
          ≤ |x| ⊓ ((k : ℝ) • e) + |x| ⊓ e :=
            inf_le_inf_add_inf_of_nonneg |x| ((k : ℝ) • e) e (abs_nonneg x) hke he
        _ = 0 := by rw [ih, hxe, add_zero]
end
end

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace WeakOrderUnit
theorem _root_.solution {e : X} (he : StrongOrderUnit e) :
    WeakOrderUnit e := by
  refine ⟨he.1, fun x hxe => ?_⟩
  rw [IsVLDisjoint, abs_of_nonneg he.1] at hxe
  obtain ⟨c, hc, hxc⟩ := he.2 x
  obtain ⟨n, hn⟩ := exists_nat_ge c
  have hxn : |x| ≤ (n : ℝ) • e :=
    hxc.trans (smul_le_smul_of_nonneg_right hn he.1)
  have hkey := abs_inf_natCast_smul_eq_zero he.1 hxe n
  have habs : |x| = 0 := by rw [← inf_eq_left.mpr hxn, hkey]
  exact (abs_eq_zero_iff_zero x).mp habs
end WeakOrderUnit
