-- Prove2me | solution 1 for QAlgorithms.Nannicini.simon_linearIndependent_prob
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:44:51.080983+00:00
-- url     : https://prove2.me/submissions/79eb93da-a314-4883-9311-478953d2ddf2

import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open Module Submodule Classical

private lemma spanning_subfamily {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {N d : ℕ} (k : Fin N → V)
    (hd : finrank (ZMod 2) V = d) (hk : span (ZMod 2) (Set.range k) = ⊤) :
    ∃ s : Fin d ↪ Fin N, LinearIndependent (ZMod 2) (k ∘ s) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' (ZMod 2) k
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = d := by
    rw [← finrank_span_eq_card hli, hspan, hk, finrank_top, hd]
  let e : Fin d ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  exact ⟨⟨a ∘ e, ha.comp e.injective⟩, hli.comp e e.injective⟩

private lemma failed_spanning_count {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] [FiniteDimensional (ZMod 2) V] (N : ℕ) :
    Fintype.card {k : Fin N → V // span (ZMod 2) (Set.range k) ≠ ⊤} * 2 ^ N ≤
      Fintype.card V ^ N * Fintype.card V := by
  classical
  let : Fintype (Module.Dual (ZMod 2) V) :=
    Fintype.ofInjective (fun f : Module.Dual (ZMod 2) V => (f : V → ZMod 2)) DFunLike.coe_injective
  let B : Finset (Fin N → V) := Finset.univ.filter fun k => span (ZMod 2) (Set.range k) ≠ ⊤
  let F : Finset (Module.Dual (ZMod 2) V) := Finset.univ.filter fun f => f ≠ 0
  let T : Module.Dual (ZMod 2) V → Finset (Fin N → V) :=
    fun f => Finset.univ.filter fun k => ∀ i, f (k i) = 0
  have hsub : B ⊆ F.biUnion T := by
    intro k hk
    have hk' : span (ZMod 2) (Set.range k) < ⊤ :=
      lt_top_iff_ne_top.mpr (Finset.mem_filter.mp hk).2
    obtain ⟨f, hf, hzero⟩ := exists_dual_map_eq_bot_of_lt_top hk' inferInstance
    refine Finset.mem_biUnion.mpr ⟨f, by simp [F, hf], ?_⟩
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    have hmem : f (k i) ∈ (⊥ : Submodule (ZMod 2) (ZMod 2)) := by
      rw [← hzero]
      exact mem_map_of_mem (subset_span ⟨i, rfl⟩)
    exact hmem
  have hcount := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  have hT (f : Module.Dual (ZMod 2) V) : (T f).card = Fintype.card (LinearMap.ker f) ^ N := by
    let e : {k : Fin N → V // ∀ i, f (k i) = 0} ≃ (Fin N → LinearMap.ker f) :=
      { toFun := fun k i => ⟨k.val i, k.property i⟩
        invFun := fun k => ⟨fun i => k i, fun i => (k i).property⟩
        left_inv := fun k => rfl
        right_inv := fun k => rfl }
    rw [show (T f).card = Fintype.card {k : Fin N → V // ∀ i, f (k i) = 0} by
      simp [T, Fintype.card_subtype]]
    rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]
  have hhalf (f : Module.Dual (ZMod 2) V) (hf : f ∈ F) :
      Fintype.card (LinearMap.ker f) * 2 = Fintype.card V := by
    have hf' : f ≠ 0 := (Finset.mem_filter.mp hf).2
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker f),
      Module.card_eq_pow_finrank (K := ZMod 2) (V := V), ZMod.card, ← Module.Dual.finrank_ker_add_one_of_ne_zero hf', pow_succ]
  have hdual : Fintype.card (Module.Dual (ZMod 2) V) = Fintype.card V := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) V),
      Module.card_eq_pow_finrank (K := ZMod 2) (V := V), Subspace.dual_finrank_eq]
  calc
    _ = B.card * 2 ^ N := by simp [B, Fintype.card_subtype]
    _ ≤ (∑ f ∈ F, (T f).card) * 2 ^ N := Nat.mul_le_mul_right _ hcount
    _ = ∑ f ∈ F, ((T f).card * 2 ^ N) := Finset.sum_mul _ _ _
    _ = ∑ _f ∈ F, Fintype.card V ^ N := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [hT, ← mul_pow, hhalf f hf]
    _ = F.card * Fintype.card V ^ N := by simp
    _ ≤ Fintype.card (Module.Dual (ZMod 2) V) * Fintype.card V ^ N :=
      Nat.mul_le_mul_right _ (Finset.card_le_univ F)
    _ = _ := by rw [hdual, Nat.mul_comm]

private lemma sampling_bound {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] [FiniteDimensional (ZMod 2) V] (N d t : ℕ)
    (hd : finrank (ZMod 2) V = d) (hN : N = d + t + 1) :
    (Fintype.card {k : Fin N → V //
      ∃ s : Fin d ↪ Fin N, LinearIndependent (ZMod 2) (k ∘ s)} : ℝ) /
      (Fintype.card (Fin N → V) : ℝ) ≥ 1 - 1 / 2 ^ (t + 1) := by
  classical
  let good : (Fin N → V) → Prop := fun k => ∃ s : Fin d ↪ Fin N, LinearIndependent (ZMod 2) (k ∘ s)
  let spans : (Fin N → V) → Prop := fun k => span (ZMod 2) (Set.range k) = ⊤
  have hle : Fintype.card {k // spans k} ≤ Fintype.card {k // good k} := by
    exact Fintype.card_subtype_mono spans good (fun k hk => spanning_subfamily k hd hk)
  have hsum : Fintype.card {k // spans k} + Fintype.card {k // ¬ spans k} =
      Fintype.card (Fin N → V) := by
    simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.sumCompl spans)
  have hc := failed_spanning_count (V := V) N
  have hv : Fintype.card V = 2 ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hd]
  have htotal : Fintype.card (Fin N → V) = (2 ^ d) ^ N := by simp [hv]
  have hpow : (2 : ℝ) ^ N = 2 ^ d * 2 ^ (t + 1) := by
    rw [hN, Nat.add_assoc, pow_add]
  have hsumR : (Fintype.card {k // spans k} : ℝ) + Fintype.card {k // ¬ spans k} =
      Fintype.card (Fin N → V) := by exact_mod_cast hsum
  have hcR : (Fintype.card {k // ¬ spans k} : ℝ) * (2 : ℝ) ^ N ≤
      (Fintype.card (Fin N → V) : ℝ) * 2 ^ d := by
    exact_mod_cast (by simpa only [spans, hv, htotal] using hc)
  have hleR : (Fintype.card {k // spans k} : ℝ) ≤ Fintype.card {k // good k} := by exact_mod_cast hle
  have htotpos : (0 : ℝ) < Fintype.card (Fin N → V) := by
    rw [htotal, Nat.cast_pow, Nat.cast_pow]; positivity
  rw [hpow] at hcR
  have hb : (Fintype.card {k // ¬ spans k} : ℝ) * 2 ^ (t + 1) ≤ Fintype.card (Fin N → V) := by
    apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < 2 ^ d by positivity)).mp
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hcR
  change (Fintype.card {k // good k} : ℝ) / (Fintype.card (Fin N → V) : ℝ) ≥ _
  apply (le_div_iff₀ htotpos).mpr
  have hp : (0 : ℝ) < 2 ^ (t + 1) := by positivity
  apply (mul_le_mul_iff_left₀ hp).mp
  field_simp
  nlinarith

theorem solution (n t : ℕ) (a : Fin n → ZMod 2) (ha : a ≠ 0) :
    (Fintype.card {k : Fin (n + t) → {v : Fin n → ZMod 2 // v ⬝ᵥ a = 0} //
        ∃ s : Fin (n - 1) ↪ Fin (n + t),
          LinearIndependent (ZMod 2) (fun i => ((k (s i) : {v : Fin n → ZMod 2 // v ⬝ᵥ a = 0}) :
            Fin n → ZMod 2))} : ℝ) /
      (Fintype.card (Fin (n + t) → {v : Fin n → ZMod 2 // v ⬝ᵥ a = 0}) : ℝ) ≥
      1 - 1 / 2 ^ (t + 1) := by
  classical
  let f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun v => v ⬝ᵥ a
      map_add' := fun x y => add_dotProduct x y a
      map_smul' := fun c x => smul_dotProduct c x a }
  have hf : f ≠ 0 := by
    intro hz
    apply ha
    ext i
    have h := congrArg (fun f : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 => f (Pi.single i 1)) hz
    simpa [f, single_dotProduct] using h
  let V := LinearMap.ker f
  have hd : finrank (ZMod 2) V = n - 1 := by
    have h : finrank (ZMod 2) V + 1 = n := by
      simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
        Module.Dual.finrank_ker_add_one_of_ne_zero hf
    omega
  have hn : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    subst n
    exact ha (Subsingleton.elim _ _)
  have hb := sampling_bound (V := V) (n + t) (n - 1) t hd (by omega)
  let e : {v : Fin n → ZMod 2 // v ⬝ᵥ a = 0} ≃ V :=
    { toFun := fun v => ⟨v.val, v.property⟩
      invFun := fun v => ⟨v.val, v.property⟩
      left_inv := fun v => rfl
      right_inv := fun v => rfl }
  let E : (Fin (n + t) → {v : Fin n → ZMod 2 // v ⬝ᵥ a = 0}) ≃ (Fin (n + t) → V) :=
    Equiv.piCongrRight (fun _ => e)
  have he (k : Fin (n + t) → {v : Fin n → ZMod 2 // v ⬝ᵥ a = 0}) :
      (∃ s : Fin (n - 1) ↪ Fin (n + t),
        LinearIndependent (ZMod 2) (fun i => (k (s i) : Fin n → ZMod 2))) ↔
      (∃ s : Fin (n - 1) ↪ Fin (n + t), LinearIndependent (ZMod 2) (E k ∘ s)) := by
    apply exists_congr
    intro s
    exact V.subtype.linearIndependent_iff (by simp)
  rw [Fintype.card_congr (Equiv.subtypeEquiv (q := fun k : Fin (n + t) → V =>
    ∃ s : Fin (n - 1) ↪ Fin (n + t), LinearIndependent (ZMod 2) (k ∘ s)) E he), Fintype.card_congr E]
  exact hb
