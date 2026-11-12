-- Prove2me | solution 1 for RLCDiscrepancy.lemma_4_12
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:13:20.489414+00:00
-- url     : https://prove2.me/submissions/835e84f9-d2df-48e4-906f-256b03ad84fd

import Mathlib
import Definitions.Def_RLCDiscrepancy_IsNormalized
import Definitions.Def_RLCDiscrepancy_relDev
import Definitions.Def_RLCDiscrepancy_selfConv
import Definitions.Def_RLCDiscrepancy_transl
import Definitions.Def_PunctSketch_coinProb

section
set_option autoImplicit false
namespace RLCDiscrepancy.Dev.L412
open RLCDiscrepancy

variable {F : Type*} [Field F] [Fintype F] {n : ℕ}

lemma card_fun_eq : (Fintype.card (Fin n → F) : ℝ) = (Fintype.card F : ℝ) ^ n := by
  simp [Fintype.card_fun]

lemma card_pos (C : Submodule F (Fin n → F)) : 0 < ((codeFinset C).card : ℝ) := by
  have : (0 : Fin n → F) ∈ codeFinset C := by simp
  exact_mod_cast Finset.card_pos.mpr ⟨_, this⟩

/-- sum over C' as sum over C × F -/
lemma sum_sup_of_not_mem (C : Submodule F (Fin n → F)) (u : Fin n → F) (hu : u ∉ C)
    (h : (Fin n → F) → ℝ) :
    ∑ p ∈ codeFinset C ×ˢ (Finset.univ : Finset F), h (p.1 + p.2 • u)
      = ∑ y ∈ codeFinset (C ⊔ Submodule.span F {u}), h y := by
  refine Finset.sum_bij (fun p _ => p.1 + p.2 • u) ?_ ?_ ?_ (fun _ _ => rfl)
  · rintro ⟨x, a⟩ hp
    simp only [Finset.mem_product, mem_codeFinset, Finset.mem_univ, and_true] at hp
    simp only [mem_codeFinset]
    exact Submodule.add_mem_sup hp (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
  · rintro ⟨x, a⟩ hp ⟨x', a'⟩ hp' he
    simp only [Finset.mem_product, mem_codeFinset, Finset.mem_univ, and_true] at hp hp'
    simp only at he
    have hax : a = a' := by
      by_contra hne
      apply hu
      have h1 : (a - a') • u = x' - x := by
        rw [sub_smul]; rw [eq_sub_iff_add_eq, sub_add_eq_add_sub, sub_eq_iff_eq_add]
        rw [← he]; abel
      have h2 : u = (a - a')⁻¹ • (x' - x) := by
        rw [← h1, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
      rw [h2]
      exact Submodule.smul_mem _ _ (C.sub_mem hp' hp)
    subst hax
    have : x = x' := by simpa using he
    rw [this]
  · intro y hy
    simp only [mem_codeFinset] at hy
    obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    exact ⟨(x, a), by simp [hx], rfl⟩

lemma sum_sup_of_mem (C : Submodule F (Fin n → F)) (u : Fin n → F) (hu : u ∈ C) :
    C ⊔ Submodule.span F {u} = C := by
  apply sup_eq_left.mpr
  rwa [Submodule.span_singleton_le_iff_mem]

lemma relDev_transl_mem (C : Submodule F (Fin n → F)) (f : (Fin n → F) → ℝ) (z : Fin n → F)
    (hz : z ∈ C) : relDev C (transl f z) = relDev C f := by
  unfold relDev transl
  congr 2
  refine Finset.sum_equiv (Equiv.addRight z) ?_ (fun _ _ => rfl)
  intro x
  simp only [mem_codeFinset, Equiv.coe_addRight]
  exact ⟨fun h => C.add_mem h hz, fun h => by simpa using C.sub_mem h hz⟩

lemma relDev_sup (C : Submodule F (Fin n → F)) (f : (Fin n → F) → ℝ) (u : Fin n → F) :
    relDev (C ⊔ Submodule.span F {u}) f
      = (∑ a : F, relDev C (transl f (a • u))) / Fintype.card F := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  by_cases hu : u ∈ C
  · rw [sum_sup_of_mem C u hu]
    have : ∀ a : F, relDev C (transl f (a • u)) = relDev C f := fun a =>
      relDev_transl_mem C f _ (C.smul_mem a hu)
    simp [this, Finset.sum_const, Finset.card_univ]
  · have hm := card_pos C
    have hs := sum_sup_of_not_mem C u hu (fun y => f y)
    have hc := sum_sup_of_not_mem C u hu (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_product, Finset.card_univ] at hc
    rw [Finset.sum_product] at hs
    simp only [Finset.sum_comm (s := codeFinset C) (t := (Finset.univ : Finset F))] at hs
    have hc' : ((codeFinset (C ⊔ Submodule.span F {u})).card : ℝ)
        = (codeFinset C).card * Fintype.card F := by
      rw [← hc]; push_cast; ring
    unfold relDev transl
    rw [← hs, hc']
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [Finset.sum_comm]
    field_simp

lemma sum_sq_g (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (C : Submodule F (Fin n → F)) :
    ∑ z, (relDev C (transl f z)) ^ 2
      = (Fintype.card F : ℝ) ^ n * relDev C (selfConv f) := by
  have hm := card_pos C
  set S := codeFinset C with hS
  set m : ℝ := (S.card : ℝ) with hmdef
  set N : ℝ := (Fintype.card F : ℝ) ^ n with hN
  have hN0 : N ≠ 0 := by
    have : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
    positivity
  have hsum := hf.2
  set A : (Fin n → F) → ℝ := fun z => ∑ x ∈ S, f (x + z) with hA
  have h1 : ∑ z, A z = m * N := by
    simp only [hA]
    rw [Finset.sum_comm]
    have : ∀ x : Fin n → F, ∑ z, f (x + z) = N := by
      intro x
      rw [hN, ← hsum]
      exact Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
    simp [this, hmdef]
  have h2 : ∑ z, A z ^ 2 = m * (N * ∑ w ∈ S, selfConv f w) := by
    have e1 : ∀ z, A z ^ 2 = ∑ x ∈ S, ∑ x' ∈ S, f (x + z) * f (x' + z) := by
      intro z; simp only [hA, sq, Finset.sum_mul_sum]
    simp only [e1]
    rw [Finset.sum_comm]
    have e2 : ∀ x ∈ S, ∑ z, ∑ x' ∈ S, f (x + z) * f (x' + z)
        = N * ∑ w ∈ S, selfConv f w := by
      intro x hx
      rw [Finset.sum_comm]
      have e3 : ∀ x' ∈ S, ∑ z, f (x + z) * f (x' + z) = N * selfConv f (x - x') := by
        intro x' _
        unfold selfConv
        rw [← hN]
        field_simp
        refine Fintype.sum_equiv (Equiv.addLeft x) _ _ ?_
        intro z
        simp only [Equiv.coe_addLeft]
        congr 2
        abel
      rw [Finset.sum_congr rfl e3, ← Finset.mul_sum]
      congr 1
      refine Finset.sum_nbij' (fun x' => x - x') (fun w => x - w) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · intro x' hx'; simp only [hS, mem_codeFinset] at hx hx' ⊢; exact C.sub_mem hx hx'
      · intro w hw; simp only [hS, mem_codeFinset] at hx hw ⊢; exact C.sub_mem hx hw
      · intro x' _; simp
      · intro w _; simp
    rw [Finset.sum_congr rfl e2]
    simp [hmdef]
  have hg : ∀ z, relDev C (transl f z) = A z / m - 1 := by
    intro z; simp [relDev, transl, hA, hmdef, hS]
  have hrd : relDev C (selfConv f) = (∑ w ∈ S, selfConv f w) / m - 1 := by
    simp [relDev, hmdef, hS]
  have e4 : ∀ z, (A z / m - 1) ^ 2 = A z ^ 2 / m ^ 2 - 2 / m * A z + 1 := by
    intro z; field_simp; ring
  simp only [hg, e4, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.mul_sum, h1, h2, hrd]
  have hcard : (Finset.univ : Finset (Fin n → F)).card = Fintype.card (Fin n → F) := rfl
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_fun_eq, ← hN]
  field_simp
  ring

end RLCDiscrepancy.Dev.L412

namespace RLCDiscrepancy
open RLCDiscrepancy.Dev.L412 in
theorem chk_lemma_4_12 {F : Type*} [Field F] [Fintype F] {n : ℕ} (f : (Fin n → F) → ℝ)
    (hf : IsNormalized f) (C : Submodule F (Fin n → F)) (hδ : relDev C f ≠ 0) (lam : ℝ)
    (hlam : 0 < lam) :
    PunctSketch.coinProb (fun u : Fin n → F =>
        |relDev C f| * (1 / (Fintype.card F : ℝ) + lam) <
          |relDev (C ⊔ Submodule.span F {u}) f|) ≤
      (((Fintype.card F : ℝ) - 1) / Fintype.card F) ^ 2 * relDev C (selfConv f) /
        (lam ^ 2 * relDev C f ^ 2) := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq1 : (1 : ℝ) < q := by rw [hq]; exact_mod_cast Fintype.one_lt_card
  have hq0 : 0 < q := by linarith
  set δ := relDev C f with hδdef
  set S : (Fin n → F) → ℝ := fun u => ∑ a ∈ Finset.univ.erase (0 : F), relDev C (transl f (a • u))
    with hSdef
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hN : (0 : ℝ) < q ^ n := by positivity
  have hcardE : ((Finset.univ.erase (0 : F)).card : ℝ) = q - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  have hg0 : relDev C (transl f ((0 : F) • (0 : Fin n → F))) = δ := by
    have : transl f ((0 : F) • (0 : Fin n → F)) = f := by
      funext x; simp [transl]
    rw [this]
  have hev : ∀ u : Fin n → F, |δ| * (1 / q + lam) < |relDev (C ⊔ Submodule.span F {u}) f| →
      (q * lam * |δ|) ^ 2 < S u ^ 2 := by
    intro u hu
    rw [relDev_sup, abs_div, abs_of_pos hq0, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))] at hu
    have hz : relDev C (transl f ((0 : F) • u)) = δ := by simpa using hg0
    rw [hz] at hu
    have hu' : |δ| * (1 + q * lam) < |δ + S u| := by
      have : |δ| * (1 / q + lam) * q = |δ| * (1 + q * lam) := by field_simp
      rw [lt_div_iff₀ hq0] at hu
      linarith
    have h3 : |δ + S u| ≤ |δ| + |S u| := abs_add_le _ _
    have h4 : q * lam * |δ| < |S u| := by nlinarith
    have h5 : 0 ≤ q * lam * |δ| := by positivity
    calc (q * lam * |δ|) ^ 2 < |S u| ^ 2 := pow_lt_pow_left₀ h4 h5 (by norm_num)
      _ = S u ^ 2 := sq_abs _
  have hsum : ∑ u, S u ^ 2 ≤ (q - 1) ^ 2 * (q ^ n * relDev C (selfConv f)) := by
    have h1 : ∀ u, S u ^ 2 ≤ (q - 1) * ∑ a ∈ Finset.univ.erase (0 : F),
        relDev C (transl f (a • u)) ^ 2 := by
      intro u
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ.erase (0 : F))
        (f := fun a => relDev C (transl f (a • u)))
      rwa [hcardE] at this
    calc ∑ u, S u ^ 2 ≤ ∑ u, (q - 1) * ∑ a ∈ Finset.univ.erase (0 : F),
          relDev C (transl f (a • u)) ^ 2 := Finset.sum_le_sum (fun u _ => h1 u)
      _ = (q - 1) * ∑ a ∈ Finset.univ.erase (0 : F), ∑ u,
          relDev C (transl f (a • u)) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
      _ = (q - 1) * ∑ a ∈ Finset.univ.erase (0 : F), ∑ z,
          relDev C (transl f z) ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl (fun a ha => ?_)
        have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
        exact Fintype.sum_bijective (fun u => a • u)
          (Finite.injective_iff_bijective.mp (smul_right_injective (Fin n → F) ha0))
          _ _ (fun _ => rfl)
      _ = (q - 1) ^ 2 * (q ^ n * relDev C (selfConv f)) := by
        rw [← sum_sq_g f hf C, Finset.sum_const, nsmul_eq_mul, hcardE]
        ring
  have hcount : ((Finset.univ.filter (fun u : Fin n → F =>
      |relDev C f| * (1 / q + lam) < |relDev (C ⊔ Submodule.span F {u}) f|)).card : ℝ)
        * (q * lam * |δ|) ^ 2 ≤ (q - 1) ^ 2 * (q ^ n * relDev C (selfConv f)) := by
    calc _ = ∑ u ∈ Finset.univ.filter (fun u : Fin n → F =>
          |relDev C f| * (1 / q + lam) < |relDev (C ⊔ Submodule.span F {u}) f|),
          (q * lam * |δ|) ^ 2 := by simp
      _ ≤ ∑ u ∈ Finset.univ.filter (fun u : Fin n → F =>
          |relDev C f| * (1 / q + lam) < |relDev (C ⊔ Submodule.span F {u}) f|), S u ^ 2 := by
        apply Finset.sum_le_sum
        intro u hu
        exact (hev u (Finset.mem_filter.mp hu).2).le
      _ ≤ ∑ u, S u ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := hsum
  unfold PunctSketch.coinProb
  rw [card_fun_eq, ← hq, div_le_iff₀ hN]
  have hd : 0 < lam ^ 2 * δ ^ 2 := by positivity
  have hpos : 0 < (q * lam * |δ|) ^ 2 := by
    have : (q * lam * |δ|) ^ 2 = q ^ 2 * (lam ^ 2 * δ ^ 2) := by rw [mul_pow, mul_pow, sq_abs]; ring
    rw [this]; positivity
  have e : (q * lam * |δ|) ^ 2 = q ^ 2 * (lam ^ 2 * δ ^ 2) := by
    rw [mul_pow, mul_pow, sq_abs]; ring
  rw [e] at hcount
  have key : ((Finset.univ.filter (fun u : Fin n → F =>
      |relDev C f| * (1 / q + lam) < |relDev (C ⊔ Submodule.span F {u}) f|)).card : ℝ)
      ≤ (q - 1) ^ 2 * (q ^ n * relDev C (selfConv f)) / (q ^ 2 * (lam ^ 2 * δ ^ 2)) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  refine key.trans (le_of_eq ?_)
  field_simp
end RLCDiscrepancy
end

theorem solution : type_of% @RLCDiscrepancy.chk_lemma_4_12 := @RLCDiscrepancy.chk_lemma_4_12
