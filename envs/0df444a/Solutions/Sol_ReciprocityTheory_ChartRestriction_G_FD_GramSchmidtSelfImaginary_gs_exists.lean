-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary.gs_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:25:56.990811+00:00
-- url     : https://prove2.me/submissions/7f189843-ecbc-403e-a20b-1bae79d3466d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpSpanRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramSchmidtSelfImaginary_perp_span
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramSchmidtSelfImaginary_perp_span_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramSchmidtSelfImaginary_coef_of_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramSchmidtSelfImaginary_hC_self_im

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
variable (hG : ∀ a b, cc (G a b) = G b a)
include hG
namespace ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
theorem _root_.solution {n : ℕ} (p : ℕ) (Y : Fin n → Fin r → ℂ) (hind : LinearIndependent ℂ Y)
    (horth : ∀ j k : Fin n, (j : ℕ) < p → p ≤ (k : ℕ) → hermC τ G (Y j) (Y k) = 0)
    (hpos : ∀ w : Fin n → ℂ, (∀ j : Fin n, p ≤ (j : ℕ) → w j = 0) → w ≠ 0 →
      0 < (hermC τ G (∑ j, w j • Y j) (∑ j, w j • Y j)).re)
    (hneg : ∀ w : Fin n → ℂ, (∀ j : Fin n, (j : ℕ) < p → w j = 0) → w ≠ 0 →
      (hermC τ G (∑ j, w j • Y j) (∑ j, w j • Y j)).re < 0) :
    ∃ g : Fin n → Fin r → ℂ,
      (∀ c a : Fin n, hermC τ G (g c) (g a) =
        if c = a then (if (c : ℕ) < p then 1 else -1) else 0) ∧
      (∀ c : Fin n, (c : ℕ) < p → g c ∈ Submodule.span ℂ (Y '' {j | (j : ℕ) < p})) ∧
      (∀ c : Fin n, g c ∈ Submodule.span ℂ (Set.range Y)) ∧
      (∀ j : Fin n, ∃ β : Fin n → ℂ, (∀ c : Fin n, ¬((c : ℕ) < p ↔ (j : ℕ) < p) → β c = 0) ∧
        Y j = ∑ c, β c • g c) := by
  classical
  obtain ⟨ε, hε⟩ : ∃ ε : Fin n → ℂ, ε = fun c : Fin n => (if (c : ℕ) < p then 1 else -1 : ℂ) :=
    ⟨fun c : Fin n => (if (c : ℕ) < p then 1 else -1 : ℂ), rfl⟩
  have hτ : ∀ a b, conj (τ (G a b)) = τ (G b a) := by
    intro a b
    rw [← hG a b]
    first
    | exact (NumberField.IsCMField.complexEmbedding_complexConj τ (G a b)).symm
    | exact (IsCMField.complexEmbedding_complexConj τ (G a b)).symm
    | (simp only [cc]; exact (NumberField.IsCMField.complexEmbedding_complexConj τ (G a b)).symm)
    | (simp [cc])
  have csym : ∀ u w, conj (hermC τ G u w) = hermC τ G w u := by
    intro u w
    simp only [hermC, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hτ]
    ring
  have smulL : ∀ (c : ℂ) u w, hermC τ G (c • u) w = c * hermC τ G u w := fun c u w =>
    map_smul (hL τ G w) c u
  have subL : ∀ u u' w, hermC τ G (u - u') w = hermC τ G u w - hermC τ G u' w := fun u u' w =>
    map_sub (hL τ G w) u u'
  have sumL : ∀ (s : Finset (Fin n)) (f : Fin n → Fin r → ℂ) w,
      hermC τ G (∑ a ∈ s, f a) w = ∑ a ∈ s, hermC τ G (f a) w := fun s f w =>
    map_sum (hL τ G w) f s
  have smulR : ∀ (c : ℂ) u w, hermC τ G u (c • w) = conj c * hermC τ G u w := by
    intro c u w
    rw [← csym, smulL, map_mul, csym]

  have cross : ∀ a c : Fin n, ¬((a : ℕ) < p ↔ (c : ℕ) < p) →
      ∀ u ∈ Submodule.span ℂ (Y '' {j | ((j : ℕ) < p ↔ (a : ℕ) < p)}),
      ∀ w ∈ Submodule.span ℂ (Y '' {j | ((j : ℕ) < p ↔ (c : ℕ) < p)}), hermC τ G u w = 0 := by
    intro a c hac u hu w hw
    refine perp_span τ G ?_ u hu
    rintro _ ⟨j, hj, rfl⟩
    refine perp_span_right τ G hG ?_ w hw
    rintro _ ⟨k, hk, rfl⟩
    simp only [Set.mem_setOf_eq] at hj hk
    by_cases hjp : (j : ℕ) < p
    · have hkp : p ≤ (k : ℕ) := by
        by_contra hkp
        exact hac ⟨fun _ => hk.mp (not_le.mp hkp), fun _ => hj.mp hjp⟩
      exact horth j k hjp hkp
    · have hkp : (k : ℕ) < p := by
        by_contra hkp
        exact hac ⟨fun ha => absurd (hj.mpr ha) hjp, fun hc => absurd (hk.mpr hc) hkp⟩
      rw [← csym, horth k j hkp (not_lt.mp hjp), map_zero]

  have step : ∀ m : ℕ, m ≤ n → ∃ g : Fin n → Fin r → ℂ,
      (∀ c a : Fin n, (c : ℕ) < m → (a : ℕ) < m → hermC τ G (g c) (g a) = if c = a then ε c else 0) ∧
      (∀ c : Fin n, (c : ℕ) < m →
        g c ∈ Submodule.span ℂ (Y '' {j | (j : ℕ) ≤ c ∧ ((j : ℕ) < p ↔ (c : ℕ) < p)})) ∧
      (∀ j : Fin n, (j : ℕ) < m →
        Y j ∈ Submodule.span ℂ (g '' {c | (c : ℕ) ≤ j ∧ ((c : ℕ) < p ↔ (j : ℕ) < p)})) := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨0, fun c _ h => absurd h (Nat.not_lt_zero _),
        fun c h => absurd h (Nat.not_lt_zero _), fun j h => absurd h (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hmn
      obtain ⟨g, horg, hspg, hspY⟩ := ih (Nat.le_of_succ_le hmn)
      set c₀ : Fin n := ⟨m, hmn⟩ with hc₀
      set T : Finset (Fin n) := Finset.univ.filter (fun a : Fin n => (a : ℕ) < m) with hT
      set v : Fin r → ℂ := Y c₀ - ∑ a ∈ T, (ε a * hermC τ G (Y c₀) (g a)) • g a with hv
      have hεsq : ∀ a, ε a * ε a = 1 := by
        intro a
        rw [hε]
        dsimp only
        split_ifs <;> norm_num
      have hvg : ∀ a ∈ T, hermC τ G v (g a) = 0 := by
        intro a ha
        have ham : (a : ℕ) < m := (Finset.mem_filter.mp ha).2
        rw [hv, subL, sumL]
        have : ∀ b ∈ T, hermC τ G ((ε b * hermC τ G (Y c₀) (g b)) • g b) (g a) =
            if b = a then hermC τ G (Y c₀) (g a) else 0 := by
          intro b hb
          rw [smulL, horg b a (Finset.mem_filter.mp hb).2 ham]
          split_ifs with hba
          · rw [hba, mul_comm (ε a), mul_assoc, hεsq, mul_one]
          · rw [mul_zero]
        rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' T a, if_pos ha, sub_self]

      set S₀ : Set (Fin n) := {j | (j : ℕ) ≤ c₀ ∧ ((j : ℕ) < p ↔ (c₀ : ℕ) < p)} with hS₀
      have hgS : ∀ a ∈ T, ((a : ℕ) < p ↔ (c₀ : ℕ) < p) → g a ∈ Submodule.span ℂ (Y '' S₀) := by
        intro a ha hblk
        have ham : (a : ℕ) < m := (Finset.mem_filter.mp ha).2
        refine Submodule.span_mono (Set.image_mono ?_) (hspg a ham)
        rintro j ⟨hj1, hj2⟩
        exact ⟨le_trans hj1 (le_of_lt ham), hj2.trans hblk⟩
      have hcoef0 : ∀ a ∈ T, ¬((a : ℕ) < p ↔ (c₀ : ℕ) < p) → hermC τ G (Y c₀) (g a) = 0 := by
        intro a ha hblk
        have ham : (a : ℕ) < m := (Finset.mem_filter.mp ha).2
        refine cross c₀ a (fun h => hblk h.symm) (Y c₀) (Submodule.subset_span ⟨c₀, Iff.rfl, rfl⟩)
          (g a) (Submodule.span_mono (Set.image_mono ?_) (hspg a ham))
        rintro j ⟨_, hj2⟩
        exact hj2
      have hvS : v ∈ Submodule.span ℂ (Y '' S₀) := by
        rw [hv]
        refine Submodule.sub_mem _ (Submodule.subset_span ⟨c₀, ⟨le_refl _, Iff.rfl⟩, rfl⟩) ?_
        refine Submodule.sum_mem _ (fun a ha => ?_)
        by_cases hblk : ((a : ℕ) < p ↔ (c₀ : ℕ) < p)
        · exact Submodule.smul_mem _ _ (hgS a ha hblk)
        · rw [hcoef0 a ha hblk, mul_zero, zero_smul]
          exact Submodule.zero_mem _
      have hv0 : v ≠ 0 := by
        intro hv0
        have hY : Y c₀ = ∑ a ∈ T, (ε a * hermC τ G (Y c₀) (g a)) • g a := by
          rw [hv] at hv0
          exact sub_eq_zero.mp hv0
        have hin : Y c₀ ∈ Submodule.span ℂ (Y '' {j | (j : ℕ) < m}) := by
          rw [hY]
          refine Submodule.sum_mem _ (fun a ha => Submodule.smul_mem _ _ ?_)
          have ham : (a : ℕ) < m := (Finset.mem_filter.mp ha).2
          refine Submodule.span_mono (Set.image_mono ?_) (hspg a ham)
          rintro j ⟨hj1, _⟩
          exact lt_of_le_of_lt hj1 ham
        have hnot : c₀ ∉ {j : Fin n | (j : ℕ) < m} := by
          simp [hc₀]
        first
        | exact hind.not_mem_span_image hnot hin
        | exact hind.notMem_span_image hnot hin

      have hsign : 0 < (ε c₀ * hermC τ G v v).re := by
        obtain ⟨w, hw, hvw⟩ := coef_of_mem Y S₀ hvS
        have hw0 : w ≠ 0 := by
          rintro rfl
          apply hv0
          rw [hvw]
          simp
        rw [hε]
        dsimp only
        by_cases hcp : (c₀ : ℕ) < p
        · rw [if_pos hcp, one_mul, hvw]
          refine hpos w (fun j hj => hw j ?_) hw0
          rintro ⟨_, hj2⟩
          exact absurd (hj2.mpr hcp) (not_lt.mpr hj)
        · rw [if_neg hcp, hvw]
          have := hneg w (fun j hj => hw j ?_) hw0
          · simp only [neg_mul, one_mul, Complex.neg_re]
            linarith
          · rintro ⟨_, hj2⟩
            exact hcp (hj2.mp hj)
      set t : ℝ := (ε c₀ * hermC τ G v v).re with ht
      have hvv : hermC τ G v v = ε c₀ * (t : ℂ) := by
        have hεc : ε c₀ = 1 ∨ ε c₀ = -1 := by
          rw [hε]
          dsimp only
          split_ifs
          · exact Or.inl rfl
          · exact Or.inr rfl
        have him := hC_self_im τ G hG v
        apply Complex.ext
        · rcases hεc with h | h <;> simp [ht, h]
        · rcases hεc with h | h <;> simp [ht, h, him]
      set s : ℂ := (((Real.sqrt t)⁻¹ : ℝ) : ℂ) with hs
      have hss : s * (conj s * (ε c₀ * (t : ℂ))) = ε c₀ := by
        have hr : ((Real.sqrt t)⁻¹ * ((Real.sqrt t)⁻¹ * t) : ℝ) = 1 := by
          rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hsign.le, inv_mul_cancel₀ hsign.ne']
        rw [hs, Complex.conj_ofReal]
        have hc : ((Real.sqrt t)⁻¹ : ℂ) * (((Real.sqrt t)⁻¹ : ℂ) * (t : ℂ)) = 1 := by
          exact_mod_cast hr
        calc ((((Real.sqrt t)⁻¹ : ℝ)) : ℂ) * ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (ε c₀ * (t : ℂ)))
            = ε c₀ * (((Real.sqrt t)⁻¹ : ℂ) * (((Real.sqrt t)⁻¹ : ℂ) * (t : ℂ))) := by
              push_cast
              ring
          _ = ε c₀ := by rw [hc, mul_one]

      refine ⟨Function.update g c₀ (s • v), ?_, ?_, ?_⟩
      · have hlt : ∀ c : Fin n, (c : ℕ) < m + 1 → c ≠ c₀ → (c : ℕ) < m := by
          intro c hc hne
          have : (c : ℕ) ≠ m := fun h => hne (Fin.ext h)
          omega
        have hTm : ∀ c : Fin n, (c : ℕ) < m → c ∈ T := fun c hc => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
        intro c a hc ha
        by_cases hc0 : c = c₀ <;> by_cases ha0 : a = c₀
        · subst hc0
          subst ha0
          rw [Function.update_self, smulL, smulR, hvv, hss, if_pos rfl]
        · subst hc0
          rw [Function.update_self, Function.update_of_ne ha0, smulL,
            hvg a (hTm a (hlt a ha ha0)), mul_zero, if_neg (Ne.symm ha0)]
        · subst ha0
          rw [Function.update_self, Function.update_of_ne hc0, smulR, ← csym,
            hvg c (hTm c (hlt c hc hc0)), map_zero, mul_zero, if_neg hc0]
        · rw [Function.update_of_ne hc0, Function.update_of_ne ha0]
          exact horg c a (hlt c hc hc0) (hlt a ha ha0)
      · intro c hc
        by_cases hc0 : c = c₀
        · subst hc0
          rw [Function.update_self]
          exact Submodule.smul_mem _ _ hvS
        · rw [Function.update_of_ne hc0]
          have : (c : ℕ) ≠ m := fun h => hc0 (Fin.ext h)
          exact hspg c (by omega)
      · intro j hj
        by_cases hj0 : j = c₀
        · subst hj0
          have hY : Y c₀ = s⁻¹ • (s • v) + ∑ a ∈ T, (ε a * hermC τ G (Y c₀) (g a)) • g a := by
            have hs0 : s ≠ 0 := by
              rw [hs]
              exact_mod_cast (inv_pos.mpr (Real.sqrt_pos.mpr hsign)).ne'
            rw [smul_smul, inv_mul_cancel₀ hs0, one_smul, hv, sub_add_cancel]
          rw [hY]
          refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span
            ⟨c₀, ⟨le_refl _, Iff.rfl⟩, Function.update_self _ _ _⟩)) ?_
          refine Submodule.sum_mem _ (fun a ha => ?_)
          have ham : (a : ℕ) < m := (Finset.mem_filter.mp ha).2
          have hac : a ≠ c₀ := fun h => by rw [h] at ham; exact lt_irrefl _ ham
          by_cases hblk : ((a : ℕ) < p ↔ (c₀ : ℕ) < p)
          · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ⟨le_of_lt ham, hblk⟩, ?_⟩)
            exact Function.update_of_ne hac _ _
          · rw [hcoef0 a ha hblk, mul_zero, zero_smul]
            exact Submodule.zero_mem _
        · have hjm : (j : ℕ) < m := by
            have : (j : ℕ) ≠ m := fun h => hj0 (Fin.ext h)
            omega
          refine Submodule.span_mono ?_ (hspY j hjm)
          rintro _ ⟨c, hc, rfl⟩
          refine ⟨c, hc, ?_⟩
          have hcc : c ≠ c₀ := by
            intro h
            rw [h] at hc
            exact absurd (lt_of_le_of_lt hc.1 hjm) (lt_irrefl _)
          exact Function.update_of_ne hcc _ _
  obtain ⟨g, horg, hspg, hspY⟩ := step n le_rfl
  refine ⟨g, fun c a => ?_, fun c hc => ?_, fun c => ?_, fun j => ?_⟩
  · rw [horg c a c.isLt a.isLt, hε]
  · refine Submodule.span_mono (Set.image_mono ?_) (hspg c c.isLt)
    rintro j ⟨_, hj2⟩
    exact hj2.mpr hc
  · refine Submodule.span_mono (Set.image_subset_range _ _) (hspg c c.isLt)
  · obtain ⟨β, hβ, hYβ⟩ := coef_of_mem g _ (hspY j j.isLt)
    refine ⟨β, fun c hc => hβ c ?_, hYβ⟩
    rintro ⟨_, h2⟩
    exact hc h2
end ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
