-- Prove2me | solution 1 for RLCDiscrepancy.lemma_4_14
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:17:39.4804+00:00
-- url     : https://prove2.me/submissions/1c359fed-f3e8-4b55-834a-6343b04f25aa

import Mathlib
import Definitions.Def_RLCDiscrepancy_IsNormalized
import Definitions.Def_RLCDiscrepancy_capacity
import Definitions.Def_RLCDiscrepancy_relDev
import Definitions.Def_RLCDiscrepancy_consSeq
import Definitions.Def_RLCDiscrepancy_IsSmooth
import Definitions.Def_RLCDiscrepancy_IsMonotone
import Definitions.Def_RLCDiscrepancy_selfConv
import Definitions.Def_RLCDiscrepancy_smoothLambda
import Definitions.Def_RLCDiscrepancy_transl
import Definitions.Def_PunctSketch_coinProb
import Theorems.Thm_RLCDiscrepancy_lemma_4_13_of_ten_le
import Theorems.Thm_RLCDiscrepancy_lemma_4_11

section
set_option autoImplicit false
namespace RLCDiscrepancy.Dev.L414b
open RLCDiscrepancy

variable {F : Type*} [Field F] [Fintype F] {n : ℕ}

lemma card_fun_eq : (Fintype.card (Fin n → F) : ℝ) = (Fintype.card F : ℝ) ^ n := by
  simp [Fintype.card_fun]

open Classical in
lemma card_filter_le_real {Ω : Type*} [Fintype Ω] (p : Ω → Prop) :
    ((Finset.univ.filter p).card : ℝ) ≤ Fintype.card Ω := by
  have h1 := Finset.card_filter_le (Finset.univ : Finset Ω) p
  rw [Finset.card_univ] at h1
  exact_mod_cast h1

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


lemma transl_transl (f : (Fin n → F) → ℝ) (a b : Fin n → F) :
    transl (transl f a) b = transl f (a + b) := by
  funext x; simp only [transl]; congr 1; abel

lemma supNorm_transl (f : (Fin n → F) → ℝ) (z : Fin n → F) :
    supNorm (transl f z) = supNorm f := by
  unfold supNorm transl
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun x _ =>
      Finset.le_sup' (fun x => |f x|) (Finset.mem_univ (x + z)))
  · refine Finset.sup'_le _ _ (fun x _ => ?_)
    have := Finset.le_sup' (fun x => |f (x + z)|) (Finset.mem_univ (x - z))
    rw [sub_add_cancel] at this
    exact this

lemma smoothLambda_transl (f : (Fin n → F) → ℝ) (z : Fin n → F) (k : ℕ) (Γ : ℝ) :
    smoothLambda (transl f z) k Γ = smoothLambda f k Γ := by
  unfold smoothLambda; rw [supNorm_transl]

lemma isNormalized_transl (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (z : Fin n → F) :
    IsNormalized (transl f z) := by
  refine ⟨fun x => hf.1 _, ?_⟩
  rw [← hf.2]
  exact Fintype.sum_equiv (Equiv.addRight z) _ _ (fun _ => rfl)

lemma consSeq_mono {k : ℕ} (u : Fin k → Fin n → F) {i l : ℕ} (h : i ≤ l) :
    consSeq u i ≤ consSeq u l :=
  Submodule.span_mono (Set.image_mono (fun j hj => lt_of_lt_of_le hj h))

lemma u_mem {k : ℕ} (u : Fin k → Fin n → F) {i l : ℕ} (hi : i < k) (h : i < l) :
    u ⟨i, hi⟩ ∈ consSeq u l :=
  Submodule.subset_span ⟨⟨i, hi⟩, by simpa using h, rfl⟩

lemma consSeq_succ {k : ℕ} (u : Fin k → Fin n → F) {i : ℕ} (hi : i < k) :
    consSeq u (i + 1) = consSeq u i ⊔ Submodule.span F {u ⟨i, hi⟩} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    have hj' : (j : ℕ) < i + 1 := hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with h | h
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨j, h, rfl⟩)
    · have : j = ⟨i, hi⟩ := Fin.ext h
      subst this
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · refine sup_le (consSeq_mono u (Nat.le_succ i)) ?_
    rw [Submodule.span_singleton_le_iff_mem]
    exact u_mem u hi (Nat.lt_succ_self i)

lemma core {k : ℕ} (u : Fin k → Fin n → F) (f : (Fin n → F) → ℝ) (j : ℕ) (hj : j ≤ k) :
    ∀ d i : ℕ, i + d = j → ∃ w ∈ consSeq u j, ∀ l, i < l → l ≤ j →
      |relDev (consSeq u l) (transl f w)| ≤ |relDev (consSeq u (l - 1)) (transl f w)| := by
  intro d
  induction d with
  | zero =>
    intro i hi
    exact ⟨0, Submodule.zero_mem _, fun l hl hl' => by omega⟩
  | succ d ih =>
    intro i hi
    obtain ⟨w, hwj, hw⟩ := ih (i + 1) (by omega)
    have hik : i < k := by omega
    have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
    set uu := u ⟨i, hik⟩ with huu
    obtain ⟨γ, -, hγ⟩ := Finset.exists_max_image (Finset.univ : Finset F)
      (fun γ => |relDev (consSeq u i) (transl (transl f w) (γ • uu))|) Finset.univ_nonempty
    refine ⟨w + γ • uu, ?_, ?_⟩
    · exact (consSeq u j).add_mem hwj ((consSeq u j).smul_mem _ (u_mem u hik (by omega)))
    · intro l hl hl'
      rw [← transl_transl]
      by_cases hl1 : l = i + 1
      · subst hl1
        simp only [Nat.add_sub_cancel]
        have hmem : γ • uu ∈ consSeq u (i + 1) :=
          (consSeq u (i + 1)).smul_mem _ (u_mem u hik (Nat.lt_succ_self i))
        rw [relDev_transl_mem _ _ _ hmem, consSeq_succ u hik, relDev_sup, abs_div,
          abs_of_pos hq, div_le_iff₀ hq]
        calc |∑ a : F, relDev (consSeq u i) (transl (transl f w) (a • uu))|
            ≤ ∑ a : F, |relDev (consSeq u i) (transl (transl f w) (a • uu))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _a : F, |relDev (consSeq u i) (transl (transl f w) (γ • uu))| :=
              Finset.sum_le_sum (fun a ha => hγ a ha)
          _ = _ := by simp [mul_comm]
      · have hl2 : i + 1 < l := by omega
        have h1 : γ • uu ∈ consSeq u l :=
          (consSeq u l).smul_mem _ (u_mem u hik (by omega))
        have h2 : γ • uu ∈ consSeq u (l - 1) :=
          (consSeq u (l - 1)).smul_mem _ (u_mem u hik (by omega))
        rw [relDev_transl_mem _ _ _ h1, relDev_transl_mem _ _ _ h2]
        exact hw l hl2 hl'

lemma exists_translate {k : ℕ} (u : Fin k → Fin n → F) (f : (Fin n → F) → ℝ) (Γ' : ℝ)
    (h : ¬ IsSmooth u f Γ' k) :
    ∃ z, IsMonotone u (transl f z) Γ' ∧ ¬ IsSmooth u (transl f z) Γ' k := by
  unfold IsSmooth at h
  push Not at h
  obtain ⟨j, hjk, hj⟩ := h
  obtain ⟨w, hwj, hw⟩ := core u f j hjk j 0 (by omega)
  have hrj : relDev (consSeq u j) (transl f w) = relDev (consSeq u j) f :=
    relDev_transl_mem _ _ _ hwj
  have hfail : ¬ IsSmooth u (transl f w) Γ' k := by
    intro hs
    have := hs j hjk
    rw [hrj] at this
    linarith
  refine ⟨w, ?_, hfail⟩
  intro l hl1 hlk hsm
  by_cases hlj : l ≤ j
  · exact hw l (by omega) hlj
  · exfalso
    have := hsm j (by omega)
    rw [hrj] at this
    linarith

end RLCDiscrepancy.Dev.L414b

namespace RLCDiscrepancy
open RLCDiscrepancy.Dev.L414b in
theorem chk_lemma_4_14 {F : Type*} [Field F] [Fintype F] (n k : ℕ) (hkn : k ≤ n)
    (f : (Fin n → F) → ℝ) (hf : IsNormalized f) (Γ : ℝ) (hΓ : 0 < Γ) (t : ℝ)
    (ht : 20 * Real.logb (Fintype.card F) n ≤ t) (htk : t ≤ k) :
    PunctSketch.coinProb (fun u : Fin k → Fin n → F =>
        IsSmooth u (selfConv f) Γ k ∧
          ¬ IsSmooth u f ((Fintype.card F : ℝ) ^ t * smoothLambda f k Γ) k) ≤
      (Fintype.card F : ℝ) ^ n * (Fintype.card F : ℝ) ^ (-(1 / 10 : ℝ) * t ^ 2) := by
  classical
  have hq2 : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hq1 : (1 : ℝ) < Fintype.card F := by linarith
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  by_cases hsmall : t ^ 2 ≤ 10 * (n : ℝ)
  · have hRHS : (1 : ℝ) ≤ (Fintype.card F : ℝ) ^ n * (Fintype.card F : ℝ) ^ (-(1 / 10 : ℝ) * t ^ 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith)]
      exact Real.one_le_rpow hq1.le (by linarith)
    refine le_trans ?_ hRHS
    unfold PunctSketch.coinProb
    rcases (Fintype.card_pos : 0 < Fintype.card (Fin k → Fin n → F)).le.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · rw [div_le_one (by exact_mod_cast h0)]
      exact card_filter_le_real _
  have ht0 : 0 ≤ t := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simpa using ht
    · refine le_trans ?_ ht
      have : (0 : ℝ) ≤ Real.logb (Fintype.card F) n :=
        Real.logb_nonneg hq1 (by exact_mod_cast h0)
      linarith
  have ht10 : 10 ≤ t := by
    by_contra hlt
    push Not at hlt
    apply hsmall
    nlinarith
  set Γ' : ℝ := (Fintype.card F : ℝ) ^ t * smoothLambda f k Γ with hΓ'
  set B : (Fin n → F) → (Fin k → Fin n → F) → Prop := fun z u =>
    IsSmooth u (selfConv f) Γ k ∧ IsMonotone u (transl f z) Γ' ∧
      ¬ IsSmooth u (transl f z) Γ' k with hB
  have hsub : Finset.univ.filter (fun u : Fin k → Fin n → F =>
        IsSmooth u (selfConv f) Γ k ∧ ¬ IsSmooth u f Γ' k) ⊆
      Finset.univ.biUnion (fun z => Finset.univ.filter (B z)) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨z, hz1, hz2⟩ := exists_translate u f Γ' hu.2
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and, hB]
    exact ⟨z, hu.1, hz1, hz2⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hΩ : (0 : ℝ) < Fintype.card (Fin k → Fin n → F) := by exact_mod_cast Fintype.card_pos
  have hone : ∀ z : Fin n → F, PunctSketch.coinProb (B z) ≤
      (Fintype.card F : ℝ) ^ (-(1 / 10 : ℝ) * t ^ 2) := by
    intro z
    have h := lemma_4_13_of_ten_le n k hkn (transl f z) (isNormalized_transl f hf z) Γ hΓ t ht htk ht10
    simp only [lemma_4_11, smoothLambda_transl] at h
    exact h
  unfold PunctSketch.coinProb
  rw [div_le_iff₀ hΩ]
  have hc : ((Finset.univ.filter (fun u : Fin k → Fin n → F =>
        IsSmooth u (selfConv f) Γ k ∧ ¬ IsSmooth u f Γ' k)).card : ℝ) ≤
      ∑ z : Fin n → F, ((Finset.univ.filter (B z)).card : ℝ) := by
    exact_mod_cast hcard
  suffices hfin : ∑ z : Fin n → F, ((Finset.univ.filter (B z)).card : ℝ) ≤
      (Fintype.card F : ℝ) ^ n * (Fintype.card F : ℝ) ^ (-(1 / 10 : ℝ) * t ^ 2) *
        Fintype.card (Fin k → Fin n → F) by
    convert hc.trans hfin
  have hz : ∀ z : Fin n → F, ((Finset.univ.filter (B z)).card : ℝ) ≤
      (Fintype.card F : ℝ) ^ (-(1 / 10 : ℝ) * t ^ 2) * Fintype.card (Fin k → Fin n → F) := by
    intro z
    have := hone z
    unfold PunctSketch.coinProb at this
    rw [div_le_iff₀ hΩ] at this
    convert this
    rfl
  refine (Finset.sum_le_sum (fun z _ => hz z)).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_fun_eq]
  ring
end RLCDiscrepancy
end

theorem solution : type_of% @RLCDiscrepancy.chk_lemma_4_14 := @RLCDiscrepancy.chk_lemma_4_14
