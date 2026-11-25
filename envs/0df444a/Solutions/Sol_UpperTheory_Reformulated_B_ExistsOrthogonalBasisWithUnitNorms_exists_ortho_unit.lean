-- Prove2me | solution 1 for UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_ortho_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:56:47.943541+00:00
-- url     : https://prove2.me/submissions/809847ca-45f0-4b5a-9bab-b8a64d20327d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsOrthogonalUnitVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.HermitianLattices.Ext.L3.WA in

private theorem UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_primitive {K V : Type} [Field K] [StarRing K] [AddCommGroup V]
    [Module K V] {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} (hS : IsHermSemilocal S)
    (hn : h.Nondegenerate) {L : AddSubgroup V} (hL : IsSelfDualMod S h L) {v : V} (hv : v ≠ 0) :
    ∃ a : K, a • v ∈ L ∧ ∃ w ∈ L, h w (a • v) = 1 := by
  let A : AddSubgroup K :=
    { carrier := {a | ∃ m ∈ L, h m v = a}
      zero_mem' := ⟨0, L.zero_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
        exact ⟨m + m', L.add_mem hm hm', by simp⟩
      neg_mem' := by
        rintro _ ⟨m, hm, rfl⟩
        exact ⟨-m, L.neg_mem hm, by simp⟩ }
  have hmul : ∀ s ∈ S, ∀ a ∈ A, s * a ∈ A := by
    rintro s hs _ ⟨m, hm, rfl⟩
    exact ⟨star s • m, hL.smul_mem _ (hS.star_mem s hs) _ hm, by
      rw [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]⟩
  have hne : ∃ a ∈ A, a ≠ 0 := by
    have hu : ∃ u, h u v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hv (hn.2 v hc)
    obtain ⟨u, hu⟩ := hu
    obtain ⟨t, ht, htu⟩ := hL.span u
    refine ⟨_, ⟨t • u, htu, rfl⟩, ?_⟩
    simp [map_smulₛₗ, ht, hu]
  have hbd : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S := by
    obtain ⟨t, ht, htv⟩ := hL.span v
    refine ⟨t, ht, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    simpa using hL.int m hm _ htv
  obtain ⟨α, ⟨w, hw, hα⟩, hα0, hdiv⟩ := hS.principal A hmul hne hbd
  refine ⟨α⁻¹, hL.dual _ fun m hm => ?_, w, hw, ?_⟩
  · simpa [mul_comm] using hdiv _ ⟨m, hm, rfl⟩
  · rw [map_smul, hα, smul_eq_mul, inv_mul_cancel₀ hα0]
open Formalism.HermitianLattices.Ext.L3.WA in

private theorem UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_extend {K V : Type} [Field K] [StarRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hS : IsHermSemilocal S) (hs : h.IsSymm) (hn : h.Nondegenerate)
    (hp : UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.PairUnit S h) {L : AddSubgroup V} (hL : IsSelfDualMod S h L)
    {k : ℕ} (hk : k < Module.finrank K V) (x : Fin k → V) (hxL : ∀ i, x i ∈ L)
    (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0) (hxu : ∀ i, IsUnitIn S (h (x i) (x i))) :
    ∃ z ∈ L, (∀ i, h (x i) z = 0) ∧ IsUnitIn S (h z z) := by
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => hs.eq u v
  let φ : V →ₗ[K] (Fin k → K) := LinearMap.pi fun i => h (x i)
  have hker : LinearMap.ker φ ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hk)
  obtain ⟨v, hvk, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hxv : ∀ i, h (x i) v = 0 := fun i => congrFun (LinearMap.mem_ker.mp hvk) i
  obtain ⟨a, hyL, w₀, hw₀, hwy⟩ := UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_primitive hS hn hL hv0
  have hxy : ∀ i, h (x i) (a • v) = 0 := fun i => by rw [map_smul, hxv, smul_zero]
  generalize a • v = y at hyL hwy hxy
  have hyx : ∀ i, h y (x i) = 0 := fun i => by rw [← hsym, hxy, star_zero]
  have hyw₀ : h y w₀ = 1 := by rw [← hsym, hwy, star_one]
  let w : V := w₀ - ∑ i, ((h (x i) (x i))⁻¹ * h (x i) w₀) • x i
  have hwL : w ∈ L :=
    L.sub_mem hw₀ (L.sum_mem fun i _ =>
      hL.smul_mem _ (S.mul_mem (hxu i).2.2 (hL.int _ (hxL i) _ hw₀)) _ (hxL i))
  have hyw : h y w = 1 := by
    simp [w, map_sub, map_sum, hyx, hyw₀]
  have hxw : ∀ j, h (x j) w = 0 := by
    intro j
    have hj := (hxu j).1
    simp only [w, map_sub, map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · field_simp
      ring
    · intro i _ hij
      rw [hxo j i hij.symm, mul_zero]
    · simp
  obtain ⟨c, hc, d, hd, hu⟩ := hp w y hyw (hL.int _ hwL _ hwL) (hL.int _ hyL _ hyL)
  refine ⟨c • w + d • y, L.add_mem (hL.smul_mem _ hc _ hwL) (hL.smul_mem _ hd _ hyL), fun i => ?_, hu⟩
  rw [map_add, map_smul, map_smul, hxw, hxy, smul_zero, smul_zero, add_zero]
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms
theorem _root_.solution :
    ∀ {K V : Type} [inst : Field K] [inst_1 : StarRing K] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} [FiniteDimensional K V],
      Formalism.HermitianLattices.Ext.L3.WA.IsHermSemilocal S →
        h.IsSymm →
          h.Nondegenerate →
            UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.PairUnit S h →
              ∀ {L : AddSubgroup V},
                Formalism.HermitianLattices.Ext.L3.WA.IsSelfDualMod S h L →
                  ∃ (x : Fin (Module.finrank K V) → V),
                    (∀ (i : Fin (Module.finrank K V)), x i ∈ L) ∧
                      (∀ (i j : Fin (Module.finrank K V)), i ≠ j → ((h : V → V →ₗ[K] K) (x i) : V → K) (x j) = (0 : K)) ∧
                        ∀ (i : Fin (Module.finrank K V)),
                          Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (((h : V → V →ₗ[K] K) (x i) : V → K) (x i)) := by
  intro K V _ _ _ _ S h _ hS hs hn hp L hL
  have key : ∀ k : ℕ, k ≤ Module.finrank K V → ∃ x : Fin k → V, (∀ i, x i ∈ L) ∧
      (∀ i j, i ≠ j → h (x i) (x j) = 0) ∧
        ∀ i, Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (h (x i) (x i)) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨x, hxL, hxo, hxu⟩ := ih (by omega)
      obtain ⟨z, hzL, hxz, hzu⟩ :=
        UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_extend hS hs hn hp hL (by omega) x hxL hxo hxu
      have hzx : ∀ i, h z (x i) = 0 := fun i => by
        rw [← hs.eq, hxz, map_zero]
      refine ⟨Fin.cons z x, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
      · refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hzL
        · simpa using hxL i
      · induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact absurd rfl hij
          | succ j => simpa using hzx j
        | succ i =>
          induction j using Fin.cases with
          | zero => simpa using hxz i
          | succ j => simpa using hxo i j fun e => hij (by rw [e])
      · refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hzu
        · simpa using hxu i
  exact key _ le_rfl
end UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms
