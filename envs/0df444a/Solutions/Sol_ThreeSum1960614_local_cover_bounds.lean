-- Prove2me | solution 1 for ThreeSum1960614.local_cover_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:13:02.517154+00:00
-- url     : https://prove2.me/submissions/fc1ccf4c-d4e8-4178-af4c-ace00d5cf773

/-
Local-cover argument adapted from c0ldzy17/three-sum-lean, commit
2b639655e07421b9ac743de9090459bab473a7c0, LocalCoverBounds.lean and LayerCounts.lean.
The finite injection and underlying formalization retain upstream attribution.
The upstream project preserves Anthropic, PBC's Apache-2.0 infrastructure notices.
-/
import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

private theorem pow_le_choose_mul (c r : ℕ) : c ^ r ≤ (c * r).choose r := by
  let graph (f : Fin r → Fin c) : Finset (Fin r × Fin c) :=
    Finset.univ.image (fun i => (i, f i))
  have hgcard (f : Fin r → Fin c) : (graph f).card = r := by
    change (Finset.univ.image (fun i : Fin r => (i, f i))).card = r
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j he
      exact congrArg Prod.fst he
  have hginj : Function.Injective graph := by
    intro f g he
    funext i
    have hm : (i, f i) ∈ graph g := by
      rw [← he]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    have hji : j = i := congrArg Prod.fst hj
    subst j
    exact (congrArg Prod.snd hj).symm
  have hcount : (Finset.univ : Finset (Fin r → Fin c)).card ≤
      ((Finset.univ : Finset (Fin r × Fin c)).powersetCard r).card := by
    apply Finset.card_le_card_of_injOn graph
    · intro f _
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hgcard f⟩
    · intro f _ g _ he
      exact hginj he
  simpa [Finset.card_powersetCard, Nat.mul_comm] using hcount

theorem solution (c h : ℕ) (hc : 3 ≤ c) (hh : 0 < h) :
    Nat.choose (c * (2 * h)) h * Nat.choose (c * (2 * h) - h) h =
      Nat.choose (c * (2 * h)) (2 * h) * Nat.choose (2 * h) h ∧
    Nat.choose (c * (2 * h) - h) h ≤ Nat.choose (c * (2 * h)) h ∧
    Nat.choose (2 * h) h < 2 ^ (2 * h) ∧
    2 ^ (2 * h) < Nat.choose (c * (2 * h)) (2 * h) ∧
    Nat.choose (c * (2 * h) - h) h ^ 2 <
      Nat.choose (c * (2 * h)) (2 * h) * 2 ^ (2 * h) := by
  have hidentity : Nat.choose (c * (2 * h)) h * Nat.choose (c * (2 * h) - h) h =
      Nat.choose (c * (2 * h)) (2 * h) * Nat.choose (2 * h) h := by
    simpa [show 2 * h - h = h by omega] using
      (Nat.choose_mul (n := c * (2 * h)) (k := 2 * h) (s := h) (by omega)).symm
  have hdegree := Nat.choose_le_choose h (Nat.sub_le (c * (2 * h)) h)
  have hgroup : Nat.choose (2 * h) h < 2 ^ (2 * h) :=
    Nat.choose_lt_two_pow _ _ (by omega)
  have houtput : 2 ^ (2 * h) < Nat.choose (c * (2 * h)) (2 * h) := by
    exact ((Nat.pow_lt_pow_iff_left (by omega : 2 * h ≠ 0)).mpr (by omega : 2 < c)).trans_le
      (pow_le_choose_mul c (2 * h))
  refine ⟨hidentity, hdegree, hgroup, houtput, ?_⟩
  calc
    Nat.choose (c * (2 * h) - h) h ^ 2 =
        Nat.choose (c * (2 * h) - h) h * Nat.choose (c * (2 * h) - h) h := by rw [pow_two]
    _ ≤ Nat.choose (c * (2 * h)) h * Nat.choose (c * (2 * h) - h) h :=
      Nat.mul_le_mul_right _ hdegree
    _ = Nat.choose (c * (2 * h)) (2 * h) * Nat.choose (2 * h) h := hidentity
    _ < Nat.choose (c * (2 * h)) (2 * h) * 2 ^ (2 * h) :=
      Nat.mul_lt_mul_of_pos_left hgroup (lt_trans (by positivity) houtput)

#print axioms solution
