-- Prove2me | solution 1 for SmallRatio.sum_mul_mod_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:14:52.496449+00:00
-- url     : https://prove2.me/submissions/c3ed8ec2-6c1b-46fc-ac0a-3c0c2061ff37

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Reciprocity

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
namespace SmallRatio
theorem _root_.solution {M : Type*} [AddCommMonoid M] (h k : ℕ) (hk : 0 < k) (hc : Nat.Coprime h k)
    (f : ℕ → M) : ∑ r ∈ range k, f (h * r % k) = ∑ r ∈ range k, f r := by
  have hinj : Set.InjOn (fun r => h * r % k) (range k : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have h1 : h * a ≡ h * b [MOD k] := hab
    have h2 : a ≡ b [MOD k] := Nat.ModEq.cancel_left_of_coprime (by
      rw [Nat.gcd_comm]; exact hc) h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 ha hb
  have himage : (range k).image (fun r => h * r % k) = range k := by
    apply eq_of_subset_of_card_le
    · intro x hx
      simp only [mem_image, mem_range] at hx
      obtain ⟨r, _, rfl⟩ := hx
      exact mem_range.2 (Nat.mod_lt _ hk)
    · rw [card_image_of_injOn hinj]
  calc ∑ r ∈ range k, f (h * r % k) = ∑ x ∈ (range k).image (fun r => h * r % k), f x :=
        (sum_image hinj).symm
    _ = ∑ r ∈ range k, f r := by rw [himage]
end SmallRatio
