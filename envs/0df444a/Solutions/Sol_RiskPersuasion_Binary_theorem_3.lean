-- Prove2me | solution 1 for RiskPersuasion.Binary.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T17:01:01.77201+00:00
-- url     : https://prove2.me/submissions/9ce0f4cb-4012-4e1a-9d95-cac183484810

import Mathlib
import Definitions.Def_RiskPersuasion_Binary_Model
import Definitions.Def_RiskPersuasion_Binary_Programs

set_option autoImplicit false

namespace RPBinaryAux
open RiskPersuasion.Binary

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

lemma e_apply (k m : Ω) : e k m = if m = k then 1 else 0 := by
  simp [e, Pi.single_apply]

lemma e_mem (k : Ω) : e k ∈ stdSimplex ℝ Ω := by
  simpa [e] using single_mem_stdSimplex (𝕜 := ℝ) k

lemma sum_e (μ : Ω → ℝ) : (∑ k, μ k • e k) = μ := by
  funext m
  simp [Finset.sum_apply, e_apply]

lemma rhat_neg_of_not_P1 (ρ : (Ω → ℝ) → Fin 2 → ℝ) {x : Ω → ℝ} (hx : x ∈ stdSimplex ℝ Ω)
    (hn : x ∉ P ρ 1) : ρhat ρ x < 0 := by
  unfold ρhat
  by_contra h
  push_neg at h
  apply hn
  refine ⟨hx, ?_⟩
  intro a'
  fin_cases a' <;> simp <;> linarith

lemma rhat_nonneg_of_P1 (ρ : (Ω → ℝ) → Fin 2 → ℝ) {x : Ω → ℝ} (hx : x ∈ P ρ 1) :
    0 ≤ ρhat ρ x := by
  have := hx.2 0
  unfold ρhat
  linarith

lemma mem_L0_of_not_K1 (ρ : (Ω → ℝ) → Fin 2 → ℝ) {k : Ω} (hk : k ∉ K1 ρ) : k ∈ L0 ρ := by
  refine ⟨?_, hk⟩
  have h := rhat_neg_of_not_P1 ρ (e_mem k) hk
  refine ⟨e_mem k, ?_⟩
  intro a'
  unfold ρhat at h
  fin_cases a' <;> simp <;> linarith

lemma not_P1_of_gt_γ (ρ : (Ω → ℝ) → Fin 2 → ℝ) (i j : Ω) {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hgt : γ ρ i j < g) : g • e i + (1 - g) • e j ∉ P ρ 1 := by
  intro hP
  have : g ≤ γ ρ i j := le_csSup ⟨1, fun x hx => hx.1.2⟩ ⟨⟨hg0, hg1⟩, hP⟩
  linarith

lemma χ_mem_P1 (ρ : (Ω → ℝ) → Fin 2 → ℝ) (hA1 : Assumption1 ρ) (i j : Ω) (hj : j ∈ K1 ρ) :
    χ ρ i j ∈ P ρ 1 := by
  set S := {g : ℝ | g ∈ Set.Icc (0:ℝ) 1 ∧ g • e i + (1 - g) • e j ∈ P ρ 1} with hS
  have hSeq : S = Set.Icc (0:ℝ) 1 ∩ (fun g : ℝ => g • e i + (1 - g) • e j) ⁻¹' P ρ 1 := rfl
  have hcl : IsClosed S := by
    rw [hSeq]
    exact isClosed_Icc.inter ((hA1 1).preimage (by fun_prop))
  have hne : S.Nonempty := by
    refine ⟨0, ⟨le_refl _, zero_le_one⟩, ?_⟩
    simp only [zero_smul, sub_zero, one_smul, zero_add]
    exact hj
  have hbdd : BddAbove S := ⟨1, fun x hx => hx.1.2⟩
  exact (hcl.csSup_mem hne hbdd).2

lemma dsum (s t : Finset Ω) (A B C D : Ω → ℝ) (M : ℝ) :
    ∑ k ∈ s, ∑ l ∈ t, (A k * B l / M + C k * D l / M) =
      ((∑ k ∈ s, A k) * (∑ l ∈ t, B l) + (∑ k ∈ s, C k) * (∑ l ∈ t, D l)) / M := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

lemma decomp (N : Set (Ω → ℝ)) (hN : Convex ℝ N) (c μ : Ω → ℝ) (hμ : μ ∈ stdSimplex ℝ Ω)
    (hc : ∑ k, μ k * c k = 0)
    (h1 : ∀ k, c k ≤ 0 → e k ∈ N)
    (h2 : ∀ k l, c k ≤ 0 → 0 < c l →
      (c l / (c l - c k)) • e k + (1 - c l / (c l - c k)) • e l ∈ N) : μ ∈ N := by
  classical
  obtain ⟨hμ0, hμ1⟩ := hμ
  set NZ := Finset.univ.filter (fun k => c k ≤ 0) with hNZ
  set PS := Finset.univ.filter (fun k => ¬ c k ≤ 0) with hPS
  have hsplit : ∀ F : Ω → ℝ, ∑ k ∈ NZ, F k + ∑ k ∈ PS, F k = ∑ k, F k :=
    fun F => Finset.sum_filter_add_sum_filter_not _ _ _
  set M := ∑ l ∈ PS, μ l * c l with hM
  have hNZc : ∑ k ∈ NZ, μ k * c k = -M := by
    have := hsplit (fun k => μ k * c k)
    rw [hc] at this
    linarith
  have hPSpos : ∀ l ∈ PS, 0 < c l := fun l hl => not_le.mp (Finset.mem_filter.mp hl).2
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun l hl => mul_nonneg (hμ0 l) (hPSpos l hl).le)
  have hμsplit : ∑ k ∈ NZ, μ k + ∑ k ∈ PS, μ k = 1 := by rw [hsplit, hμ1]
  have hesplit : ∀ m, ∑ k ∈ NZ, μ k * e k m + ∑ k ∈ PS, μ k * e k m = μ m := by
    intro m
    rw [hsplit]
    simp [e_apply]
  rcases hM0.lt_or_eq with hMpos | hMz
  · have hNZneg : ∑ k ∈ NZ, μ k * -c k = M := by
      simp only [mul_neg, Finset.sum_neg_distrib, hNZc, neg_neg]
    have hrepr : μ = ∑ p ∈ NZ ×ˢ PS, (μ p.1 * μ p.2 * (c p.2 - c p.1) / M) •
        ((c p.2 / (c p.2 - c p.1)) • e p.1 + (1 - c p.2 / (c p.2 - c p.1)) • e p.2) := by
      funext m
      rw [Finset.sum_apply, Finset.sum_product]
      have hterm : ∀ k ∈ NZ, ∀ l ∈ PS,
          ((μ k * μ l * (c l - c k) / M) •
            ((c l / (c l - c k)) • e k + (1 - c l / (c l - c k)) • e l)) m =
          (μ k * e k m) * (μ l * c l) / M + (μ k * -c k) * (μ l * e l m) / M := by
        intro k hk l hl
        have hck : c k ≤ 0 := (Finset.mem_filter.mp hk).2
        have hcl := hPSpos l hl
        have hne : c l - c k ≠ 0 := by linarith
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        field_simp
        ring
      rw [Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun l hl => hterm k hk l hl)),
        dsum, ← hM, hNZneg]
      rw [← hesplit m]
      field_simp
    rw [hrepr]
    apply hN.sum_mem
    · intro p hp
      rw [Finset.mem_product] at hp
      have h1' : c p.1 ≤ 0 := (Finset.mem_filter.mp hp.1).2
      have h2' := hPSpos p.2 hp.2
      apply div_nonneg _ hMpos.le
      exact mul_nonneg (mul_nonneg (hμ0 _) (hμ0 _)) (by linarith)
    · rw [Finset.sum_product]
      have hw : ∀ k l, μ k * μ l * (c l - c k) / M =
          μ k * (μ l * c l) / M + (μ k * -c k) * μ l / M := by intros; ring
      simp_rw [hw]
      rw [dsum, ← hM, hNZneg, mul_comm M, ← add_mul, hμsplit, one_mul, div_self hMpos.ne']
    · intro p hp
      rw [Finset.mem_product] at hp
      exact h2 p.1 p.2 (Finset.mem_filter.mp hp.1).2 (hPSpos p.2 hp.2)
  · have hPS0 : ∀ l ∈ PS, μ l = 0 := by
      intro l hl
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun l hl => mul_nonneg (hμ0 l) (hPSpos l hl).le)).mp hMz.symm l hl
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · linarith [hPSpos l hl]
    have hNZ1 : ∑ k ∈ NZ, μ k = 1 := by
      rw [Finset.sum_eq_zero hPS0] at hμsplit
      linarith
    have hrepr : μ = ∑ k ∈ NZ, μ k • e k := by
      funext m
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      have := hesplit m
      rw [Finset.sum_eq_zero (s := PS) (fun k hk => by rw [hPS0 k hk, zero_mul]), add_zero] at this
      exact this.symm
    rw [hrepr]
    exact hN.sum_mem (fun k _ => hμ0 k) hNZ1 (fun k hk => h1 k (Finset.mem_filter.mp hk).2)

lemma P1_sub_hull (ρ : (Ω → ℝ) → Fin 2 → ℝ) (hA2 : Assumption2 ρ) :
    P ρ 1 ⊆ convexHull ℝ (e '' K1 ρ ∪ K01 ρ) := by
  intro μ hμP
  by_contra hC
  have hfin : (e '' K1 ρ ∪ K01 ρ).Finite := by
    apply Set.Finite.union (Set.toFinite _)
    apply (Set.finite_range (fun p : Ω × Ω => χ ρ p.1 p.2)).subset
    rintro x ⟨i, -, j, -, rfl⟩
    exact ⟨(i, j), rfl⟩
  have hcl : IsClosed (convexHull ℝ (e '' K1 ρ ∪ K01 ρ)) := (hfin.isCompact_convexHull ℝ).isClosed
  obtain ⟨f, u, hfμ, hfC⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _) hcl hC
  have hlin : ∀ x : Ω → ℝ, f x = ∑ k, x k * f (e k) := by
    intro x
    conv_lhs => rw [← sum_e x]
    rw [map_sum]
    simp [map_smul]
  set c : Ω → ℝ := fun k => f (e k) - f μ with hc
  have hK1 : ∀ j ∈ K1 ρ, 0 < c j := by
    intro j hj
    have := hfC (e j) (subset_convexHull ℝ _ (Or.inl ⟨j, hj, rfl⟩))
    simp only [hc]
    linarith
  have hχ : ∀ i ∈ L0 ρ, ∀ j ∈ K1 ρ, 0 < γ ρ i j * c i + (1 - γ ρ i j) * c j := by
    intro i hi j hj
    have h := hfC (χ ρ i j) (subset_convexHull ℝ _ (Or.inr ⟨i, hi, j, hj, rfl⟩))
    have hfχ : f (χ ρ i j) = γ ρ i j * f (e i) + (1 - γ ρ i j) * f (e j) := by
      simp [χ, map_add, map_smul]
    have : γ ρ i j * c i + (1 - γ ρ i j) * c j = f (χ ρ i j) - f μ := by
      rw [hfχ]; simp only [hc]; ring
    rw [this]
    linarith
  have hsum : ∑ k, μ k * c k = 0 := by
    simp only [hc, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hμP.1.2, ← hlin μ]
    ring
  have hnotK1 : ∀ k, c k ≤ 0 → k ∉ K1 ρ := fun k hk hK => by linarith [hK1 k hK]
  have h1 : ∀ k, c k ≤ 0 → e k ∈ {x : Ω → ℝ | x ∈ stdSimplex ℝ Ω ∧ ρhat ρ x < 0} :=
    fun k hk => ⟨e_mem k, rhat_neg_of_not_P1 ρ (e_mem k) (hnotK1 k hk)⟩
  have h2 : ∀ k l, c k ≤ 0 → 0 < c l →
      (c l / (c l - c k)) • e k + (1 - c l / (c l - c k)) • e l ∈
        {x : Ω → ℝ | x ∈ stdSimplex ℝ Ω ∧ ρhat ρ x < 0} := by
    intro k l hk hl
    have hden : 0 < c l - c k := by linarith
    set g := c l / (c l - c k) with hg
    have hg0 : 0 ≤ g := div_nonneg hl.le hden.le
    have hg1 : g ≤ 1 := by rw [hg, div_le_one hden]; linarith
    by_cases hlK : l ∈ K1 ρ
    · have hkL := mem_L0_of_not_K1 ρ (hnotK1 k hk)
      have hpos := hχ k hkL l hlK
      have hzero : g * c k + (1 - g) * c l = 0 := by
        rw [hg]; field_simp; ring
      have hgt : γ ρ k l < g := by
        by_contra hle
        push_neg at hle
        have : (g - γ ρ k l) * (c l - c k) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
        have hid : (g - γ ρ k l) * (c l - c k) =
            (γ ρ k l * c k + (1 - γ ρ k l) * c l) - (g * c k + (1 - g) * c l) := by ring
        linarith
      have hS : g • e k + (1 - g) • e l ∈ stdSimplex ℝ Ω :=
        (convex_stdSimplex (𝕜 := ℝ) (ι := Ω)) (e_mem k) (e_mem l) hg0 (by linarith) (by ring)
      exact ⟨hS, rhat_neg_of_not_P1 ρ hS (not_P1_of_gt_γ ρ k l hg0 hg1 hgt)⟩
    · have hel : e l ∈ {x : Ω → ℝ | x ∈ stdSimplex ℝ Ω ∧ ρhat ρ x < 0} :=
        ⟨e_mem l, rhat_neg_of_not_P1 ρ (e_mem l) hlK⟩
      exact hA2 (h1 k hk) hel hg0 (by linarith) (by ring)
  have hmem := decomp _ hA2 c μ hμP.1 hsum h1 h2
  exact absurd hmem.2 (not_lt.mpr (rhat_nonneg_of_P1 ρ hμP))

lemma hull_nonneg (S : Set (Ω → ℝ)) (hS : S ⊆ stdSimplex ℝ Ω) {x : Ω → ℝ}
    (hx : x ∈ convexHull ℝ (S ∪ {0})) : ∀ ω, 0 ≤ x ω := by
  have : convexHull ℝ (S ∪ {0}) ⊆ {y : Ω → ℝ | ∀ ω, 0 ≤ y ω} := by
    apply convexHull_min
    · rintro y (hy | hy)
      · exact (hS hy).1
      · rw [Set.mem_singleton_iff.mp hy]
        intro ω
        simp
    · intro y hy z hz a b ha hb _ ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hy ω)) (mul_nonneg hb (hz ω))
  exact this hx

lemma seg_repr (S : Set (Ω → ℝ)) {x : Ω → ℝ} (hx : x ∈ convexHull ℝ (S ∪ {0})) :
    ∃ b : ℝ, ∃ y : Ω → ℝ, 0 ≤ b ∧ b ≤ 1 ∧ (b ≠ 0 → y ∈ convexHull ℝ S) ∧ x = b • y := by
  rcases S.eq_empty_or_nonempty with h | h
  · subst h
    simp only [Set.empty_union, convexHull_singleton, Set.mem_singleton_iff] at hx
    exact ⟨0, 0, le_rfl, zero_le_one, fun h => absurd rfl h, by simp [hx]⟩
  · rw [Set.union_singleton, convexHull_insert h, mem_convexJoin] at hx
    obtain ⟨a, ha, y, hy, hseg⟩ := hx
    rw [Set.mem_singleton_iff.mp ha] at hseg
    obtain ⟨a', b, ha', hb, hab, rfl⟩ := hseg
    exact ⟨b, y, hb, by linarith, fun _ => hy, by simp⟩

lemma combo_mem (V : Set (Ω → ℝ)) (y : Ω → ℝ) (b : ℝ) (hb : 0 ≤ b) (hy : b ≠ 0 → y ∈ V)
    (r : Ω → ℝ) (hr0 : ∀ ω, 0 ≤ r ω) (hrV : ∀ ω, r ω ≠ 0 → e ω ∈ V)
    (hs : b + ∑ ω, r ω ≤ 1) : b • y + r ∈ convexHull ℝ (V ∪ {0}) := by
  classical
  let w : Option (Option Ω) → ℝ := fun o =>
    Option.elim o (1 - b - ∑ ω, r ω) (fun o' => Option.elim o' b r)
  let z : Option (Option Ω) → Ω → ℝ := fun o =>
    Option.elim o 0 (fun o' => Option.elim o' (if y ∈ V then y else 0)
      (fun ω => if e ω ∈ V then e ω else 0))
  have hrepr : b • y + r = ∑ o, w o • z o := by
    rw [Fintype.sum_option, Fintype.sum_option]
    simp only [w, z, Option.elim, smul_zero, zero_add]
    congr 1
    · by_cases h : y ∈ V
      · simp [h]
      · have : b = 0 := by
          by_contra hb'
          exact h (hy hb')
        simp [h, this]
    · conv_lhs => rw [← sum_e r]
      refine Finset.sum_congr rfl (fun ω _ => ?_)
      by_cases h : e ω ∈ V
      · simp [h]
      · have : r ω = 0 := by
          by_contra h'
          exact h (hrV ω h')
        simp [h, this]
  rw [hrepr]
  apply (convex_convexHull ℝ _).sum_mem
  · intro o _
    rcases o with _ | _ | ω
    · simp only [w, Option.elim]; linarith [Finset.sum_nonneg (fun ω (_ : ω ∈ Finset.univ) => hr0 ω)]
    · exact hb
    · exact hr0 ω
  · rw [Fintype.sum_option, Fintype.sum_option]
    simp only [w, Option.elim]
    ring
  · intro o _
    apply subset_convexHull
    rcases o with _ | _ | ω
    · exact Or.inr rfl
    · simp only [z, Option.elim]
      split_ifs with h
      · exact Or.inl h
      · exact Or.inr rfl
    · simp only [z, Option.elim]
      split_ifs with h
      · exact Or.inl h
      · exact Or.inr rfl

end RPBinaryAux

open RiskPersuasion.Binary in
theorem solution {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (ρ : (Ω → ℝ) → Fin 2 → ℝ) (v : Ω → Fin 2 → ℝ) (μstar : Ω → ℝ)
    (hμ : μstar ∈ stdSimplex ℝ Ω) (hv : ∀ ω, v ω 0 ≤ v ω 1)
    (hA1 : Assumption1 ρ) (hA2 : Assumption2 ρ) :
    (∀ t : Fin 2 → Ω → ℝ, Feasible10 ρ μstar t → Feasible7 ρ μstar t) ∧
      (∀ t : Fin 2 → Ω → ℝ, Feasible7 ρ μstar t →
        ∃ t' : Fin 2 → Ω → ℝ, Feasible10 ρ μstar t' ∧ objective v t ≤ objective v t') := by
  classical
  have hL0P0 : e '' L0 ρ ⊆ P ρ 0 := by
    rintro _ ⟨ω, hω, rfl⟩
    exact hω.1
  have hVP1 : e '' K1 ρ ∪ K01 ρ ⊆ P ρ 1 := by
    rintro _ (⟨ω, hω, rfl⟩ | ⟨i, -, j, hj, rfl⟩)
    · exact hω
    · exact RPBinaryAux.χ_mem_P1 ρ hA1 i j hj
  refine ⟨?_, ?_⟩
  · rintro t ⟨h1, h0, hs⟩
    refine ⟨fun ω => by simp [Fin.sum_univ_two, hs ω], Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · exact convexHull_mono (Set.union_subset_union_left _ hL0P0) h0
    · exact convexHull_mono (Set.union_subset_union_left _ hVP1) h1
  · rintro t ⟨hsum, hhull⟩
    have ht0 := hhull 0
    have ht1 := hhull 1
    have hsum' : ∀ ω, t 0 ω + t 1 ω = μstar ω := fun ω => by
      simpa [Fin.sum_univ_two] using hsum ω
    have hPS : ∀ a, P ρ a ⊆ stdSimplex ℝ Ω := fun a x hx => hx.1
    have n0 := RPBinaryAux.hull_nonneg _ (hPS 0) ht0
    have n1 := RPBinaryAux.hull_nonneg _ (hPS 1) ht1
    have htot : ∑ ω, t 0 ω + ∑ ω, t 1 ω = 1 := by
      rw [← Finset.sum_add_distrib]
      simp_rw [hsum']
      exact hμ.2
    have ht1nn : 0 ≤ ∑ ω, t 1 ω := Finset.sum_nonneg (fun ω _ => n1 ω)
    set r : Ω → ℝ := fun ω => if ω ∈ L0 ρ then 0 else t 0 ω with hr
    set s0 : Ω → ℝ := fun ω => if ω ∈ L0 ρ then t 0 ω else 0 with hs0
    have hr0 : ∀ ω, 0 ≤ r ω := fun ω => by
      simp only [hr]; split_ifs
      · exact le_rfl
      · exact n0 ω
    have hs00 : ∀ ω, 0 ≤ s0 ω := fun ω => by
      simp only [hs0]; split_ifs
      · exact n0 ω
      · exact le_rfl
    have hr_le : ∑ ω, r ω ≤ ∑ ω, t 0 ω := Finset.sum_le_sum (fun ω _ => by
      simp only [hr]; split_ifs
      · exact n0 ω
      · exact le_rfl)
    have hs0_le : ∑ ω, s0 ω ≤ ∑ ω, t 0 ω := Finset.sum_le_sum (fun ω _ => by
      simp only [hs0]; split_ifs
      · exact le_rfl
      · exact n0 ω)
    refine ⟨![s0, fun ω => t 1 ω + r ω], ⟨?_, ?_, ?_⟩, ?_⟩
    · show (fun ω => t 1 ω + r ω) ∈ _
      obtain ⟨b, y, hb0, hb1, hy, hty⟩ := RPBinaryAux.seg_repr _ ht1
      have hyV : b ≠ 0 → y ∈ convexHull ℝ (e '' K1 ρ ∪ K01 ρ) := fun hb =>
        convexHull_min (RPBinaryAux.P1_sub_hull ρ hA2) (convex_convexHull ℝ _) (hy hb)
      have hbt : ∑ ω, t 1 ω = b := by
        by_cases hb : b = 0
        · rw [hty, hb]; simp
        · have hyS : y ∈ stdSimplex ℝ Ω :=
            convexHull_min (hPS 1) (convex_stdSimplex (𝕜 := ℝ) (ι := Ω)) (hy hb)
          rw [hty]
          simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hyS.2, mul_one]
      have hrV : ∀ ω, r ω ≠ 0 → e ω ∈ convexHull ℝ (e '' K1 ρ ∪ K01 ρ) := by
        intro ω hω
        have hnL : ω ∉ L0 ρ := fun h => hω (by simp only [hr, if_pos h])
        have hK : ω ∈ K1 ρ := by
          by_contra hK
          exact hnL (RPBinaryAux.mem_L0_of_not_K1 ρ hK)
        exact subset_convexHull ℝ _ (Or.inl ⟨ω, hK, rfl⟩)
      have hmass : b + ∑ ω, r ω ≤ 1 := by linarith
      have hc := RPBinaryAux.combo_mem (convexHull ℝ (e '' K1 ρ ∪ K01 ρ)) y b hb0 hyV r hr0 hrV hmass
      have hsub : convexHull ℝ (convexHull ℝ (e '' K1 ρ ∪ K01 ρ) ∪ {0}) ⊆
          convexHull ℝ (e '' K1 ρ ∪ K01 ρ ∪ {0}) :=
        convexHull_min (Set.union_subset (convexHull_mono Set.subset_union_left)
          (Set.Subset.trans Set.subset_union_right (subset_convexHull ℝ _)))
          (convex_convexHull ℝ _)
      have heq : (fun ω => t 1 ω + r ω) = b • y + r := by
        funext ω
        rw [hty]
        rfl
      rw [heq]
      exact hsub hc
    · show s0 ∈ _
      have hrV : ∀ ω, s0 ω ≠ 0 → e ω ∈ e '' L0 ρ := by
        intro ω hω
        by_cases h : ω ∈ L0 ρ
        · exact ⟨ω, h, rfl⟩
        · exact absurd (by simp only [hs0, if_neg h]) hω
      have := RPBinaryAux.combo_mem (e '' L0 ρ) 0 0 le_rfl (fun h => absurd rfl h) s0 hs00 hrV
        (by linarith)
      simpa using this
    · intro ω
      show s0 ω + (t 1 ω + r ω) = μstar ω
      simp only [hs0, hr]
      split_ifs <;> linarith [hsum' ω]
    · unfold objective
      apply Finset.sum_le_sum
      intro ω _
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        hs0, hr]
      split_ifs
      · linarith
      · nlinarith [hv ω, n0 ω]
