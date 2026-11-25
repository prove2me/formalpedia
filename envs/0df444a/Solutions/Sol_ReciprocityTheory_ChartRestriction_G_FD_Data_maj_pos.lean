-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.maj_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:39:51.776966+00:00
-- url     : https://prove2.me/submissions/bba5a9e8-cdb4-487a-bd21-7fb3ed6d166f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_eq_two_ppos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_zero_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_quad_re_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Data
variable {r : ℕ} (X : Data E r)
private theorem hermC_smul_left_embedding (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ)
    (u w : Fin r → ℂ) : hermC τ G (c • u) w = c * hermC τ G u w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
private theorem hermC_finset_sum_left' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*}
    [Fintype ι] (c : ι → ℂ) (u : ι → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ i, c i • u i) w = ∑ i, c i * hermC τ G (u i) w := by
  simp only [hermC, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
  simp only [mul_assoc]
private theorem hermC_finset_sum_right_of_conj_symm (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) {ι : Type*} [Fintype ι] (c : ι → ℂ) (u : ι → Fin r → ℂ)
    (w : Fin r → ℂ) : hermC τ G w (∑ i, c i • u i) = ∑ i, conj (c i) * hermC τ G w (u i) := by
  rw [← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ hG, hermC_finset_sum_left', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ hG]
private theorem hermC_smul_right_of_conj_symm (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) (c : ℂ) (u w : Fin r → ℂ) :
    hermC τ G w (c • u) = conj c * hermC τ G w u := by
  rw [← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ hG, hermC_smul_left_embedding, map_mul,
    ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ hG]
private theorem hermC_sum_smul_sum_smul_of_conj_symm (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) {ι : Type*} [Fintype ι] (c : ι → ℂ) (u : ι → Fin r → ℂ) :
    hermC τ G (∑ i, c i • u i) (∑ i, c i • u i) =
      ∑ i, ∑ j, c i * hermC τ G (u i) (u j) * conj (c j) := by
  rw [hermC_finset_sum_left']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hermC_finset_sum_right_of_conj_symm τ hG, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
end Data
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) {v : Fin r → ℂ} (hv : v ≠ 0) :
    0 < X.maj x τ v := by
  classical
  have hG := X.Gm_herm
  have hApd : (X.gramPos x τ).PosDef := X.gramPos_posDef hx τ
  have hAdef : ∀ a b, hermC τ.1 X.Gm (X.colP x τ a) (X.colP x τ b) = X.gramPos x τ a b :=
    fun a b => rfl
  have hAinv : (X.gramPos x τ)⁻¹ * X.gramPos x τ = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hApd.isUnit)

  have hquadP : ∀ c : Fin X.p0 → ℂ,
      hermC τ.1 X.Gm (∑ a, c a • X.colP x τ a) (∑ a, c a • X.colP x τ a) =
        ∑ a, ∑ b, c a * X.gramPos x τ a b * conj (c b) :=
    fun c => hermC_sum_smul_sum_smul_of_conj_symm τ.1 hG c (X.colP x τ)
  have hnnP : ∀ c : Fin X.p0 → ℂ, 0 ≤ (∑ a, ∑ b, c a * X.gramPos x τ a b * conj (c b)).re := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp
    · exact (ReciprocityTheory.ChartRestriction.G.FD.quad_re_pos hApd hc).le

  have hneg : ∀ w : Fin r → ℂ, (∀ a, hermC τ.1 X.Gm w (X.colP x τ a) = 0) → w ≠ 0 →
      (hermC τ.1 X.Gm w w).re < 0 := by
    intro w hw0 hwne
    by_contra hcon
    have hcon' := not_lt.mp hcon
    obtain ⟨P, -, hP⟩ := X.signature τ
    let ip : Fin (r - X.p0) → Fin r := fun b => ⟨X.p0 + b.1, by have := b.2; omega⟩
    let pc : Fin (r - X.p0) → Fin r → ℂ := fun b => col P (ip b)
    have hpc : ∀ b b', hermC τ.1 X.Gm (pc b) (pc b') =
        -(1 : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) b b' := by
      intro b b'
      have h := congrFun (congrFun hP (ip b)) (ip b')
      change hermC τ.1 X.Gm (pc b) (pc b') = _ at h
      rw [h]
      by_cases hbb : b = b'
      · subst hbb
        rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        simp [ip, sgn]
      · have hne : ip b ≠ ip b' := by
          intro heq
          exact hbb (Fin.ext (by simpa [ip] using congrArg Fin.val heq))
        rw [Matrix.diagonal_apply_ne _ hne, Matrix.one_apply_ne hbb, neg_zero]
    have hquadN : ∀ d : Fin (r - X.p0) → ℂ,
        hermC τ.1 X.Gm (∑ b, d b • pc b) (∑ b, d b • pc b) =
          -(∑ b, ∑ b', d b * (1 : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) b b' * conj (d b')) := by
      intro d
      rw [hermC_sum_smul_sum_smul_of_conj_symm τ.1 hG, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [hpc]
      ring
    have hwY : ∀ c : Fin X.p0 → ℂ, hermC τ.1 X.Gm w (∑ a, c a • X.colP x τ a) = 0 := by
      intro c
      rw [hermC_finset_sum_right_of_conj_symm τ.1 hG]
      simp [hw0]
    have hYw : ∀ c : Fin X.p0 → ℂ, hermC τ.1 X.Gm (∑ a, c a • X.colP x τ a) w = 0 := by
      intro c
      rw [← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 hG, hwY, map_zero]

    let f : Option (Fin X.p0) ⊕ Fin (r - X.p0) → Fin r → ℂ :=
      Sum.elim (fun o => Option.elim o w (X.colP x τ)) pc
    have hnli : ¬ LinearIndependent ℂ f := by
      intro hli
      have h := hli.fintype_card_le_finrank
      have hp := X.p0_le
      simp at h <;> omega
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnli
    rw [Fintype.sum_sum_type, Fintype.sum_option] at hg
    simp only [f, Sum.elim_inl, Sum.elim_inr, Option.elim_none, Option.elim_some] at hg
    have hu : g (Sum.inl none) • w + ∑ a, g (Sum.inl (some a)) • X.colP x τ a =
        ∑ b, (-g (Sum.inr b)) • pc b := by
      rw [eq_neg_of_add_eq_zero_left hg]
      simp only [neg_smul, Finset.sum_neg_distrib]
    have hUU : 0 ≤ (hermC τ.1 X.Gm (g (Sum.inl none) • w + ∑ a, g (Sum.inl (some a)) • X.colP x τ a)
        (g (Sum.inl none) • w + ∑ a, g (Sum.inl (some a)) • X.colP x τ a)).re := by
      simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left, ReciprocityTheory.ChartRestriction.G.FD.hermC_add_right,
        hermC_smul_left_embedding, hermC_smul_right_of_conj_symm τ.1 hG, hwY, hYw, mul_zero, add_zero, zero_add]
      rw [Complex.add_re]
      apply add_nonneg
      · have e : (conj (g (Sum.inl none)) * (g (Sum.inl none) * hermC τ.1 X.Gm w w)).re =
            Complex.normSq (g (Sum.inl none)) * (hermC τ.1 X.Gm w w).re := by
          rw [← mul_assoc, mul_comm (conj (g (Sum.inl none))) (g (Sum.inl none)), Complex.mul_conj]
          simp
        rw [e]
        exact mul_nonneg (Complex.normSq_nonneg _) hcon'
      · rw [hquadP]
        exact hnnP _
    have hdz : (fun b => -g (Sum.inr b)) = 0 := by
      by_contra hd
      have hpos := ReciprocityTheory.ChartRestriction.G.FD.quad_re_pos Matrix.PosDef.one hd
      beta_reduce at hpos
      rw [hu, hquadN, Complex.neg_re] at hUU
      linarith
    have hgb : ∀ b, g (Sum.inr b) = 0 := fun b => by simpa using congrFun hdz b
    have hu0 : g (Sum.inl none) • w + ∑ a, g (Sum.inl (some a)) • X.colP x τ a = 0 := by
      rw [hu]
      simp [hgb]
    have hYY : hermC τ.1 X.Gm (∑ a, g (Sum.inl (some a)) • X.colP x τ a)
        (∑ a, g (Sum.inl (some a)) • X.colP x τ a) = 0 := by
      have h0 : hermC τ.1 X.Gm (g (Sum.inl none) • w + ∑ a, g (Sum.inl (some a)) • X.colP x τ a)
          (∑ a, g (Sum.inl (some a)) • X.colP x τ a) = 0 := by
        rw [hu0]
        exact ReciprocityTheory.ChartRestriction.G.FD.hermC_zero_left _ _ _
      rw [ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left, hermC_smul_left_embedding, hwY, mul_zero, zero_add] at h0
      exact h0
    have hga : (fun a => g (Sum.inl (some a))) = 0 := by
      by_contra hd
      have hpos := ReciprocityTheory.ChartRestriction.G.FD.quad_re_pos hApd hd
      beta_reduce at hpos
      rw [hquadP] at hYY
      rw [hYY] at hpos
      simp at hpos
    have hgas : ∀ a, g (Sum.inl (some a)) = 0 := fun a => by simpa using congrFun hga a
    have hg0 : g (Sum.inl none) = 0 := by
      have h := hu0
      simp only [hgas, zero_smul, Finset.sum_const_zero, add_zero] at h
      exact (smul_eq_zero.mp h).resolve_right hwne
    obtain (_ | a) | b := i
    · exact hi hg0
    · exact hi (hgas a)
    · exact hi (hgb b)

  have horth : ∀ a, hermC τ.1 X.Gm (v - X.ppos x τ v) (X.colP x τ a) = 0 := by
    intro a
    have hmul : ∀ b, ∑ c, (X.gramPos x τ)⁻¹ b c * X.gramPos x τ c a = if b = a then 1 else 0 := by
      intro b
      have := congrFun (congrFun hAinv b) a
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      exact this
    rw [ReciprocityTheory.ChartRestriction.G.FD.hermC_sub_left, X.ppos_eq, hermC_finset_sum_left']
    simp only [hAdef, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc, ← Finset.mul_sum, hmul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, sub_self]
  obtain ⟨w, hw⟩ : ∃ w, w = v - X.ppos x τ v := ⟨_, rfl⟩
  have horth' : ∀ a, hermC τ.1 X.Gm w (X.colP x τ a) = 0 := by
    intro a
    rw [hw]
    exact horth a
  have hwy : hermC τ.1 X.Gm w (X.ppos x τ v) = 0 := by
    rw [X.ppos_eq x τ v, hermC_finset_sum_right_of_conj_symm τ.1 hG]
    simp [horth']
  have hyw : hermC τ.1 X.Gm (X.ppos x τ v) w = 0 := by
    rw [← ReciprocityTheory.ChartRestriction.G.FD.hermC_conj τ.1 hG, hwy, map_zero]
  have hvdec : v = X.ppos x τ v + w := by
    rw [hw]
    abel
  have hHf := X.Hf_self hx τ v
  rw [X.Hf_eq_two_ppos] at hHf
  obtain ⟨y, hy⟩ : ∃ y, y = X.ppos x τ v := ⟨_, rfl⟩
  have hyq : y = ∑ a, (∑ b, hermC τ.1 X.Gm v (X.colP x τ b) * (X.gramPos x τ)⁻¹ b a) •
      X.colP x τ a := by
    rw [hy]
    exact X.ppos_eq x τ v
  have hyy_nn : 0 ≤ (hermC τ.1 X.Gm y y).re := by
    rw [hyq, hquadP]
    exact hnnP _
  have hyy_pos : y ≠ 0 → 0 < (hermC τ.1 X.Gm y y).re := by
    intro hy0
    rw [hyq, hquadP]
    apply ReciprocityTheory.ChartRestriction.G.FD.quad_re_pos hApd
    intro hc
    apply hy0
    rw [hyq]
    refine Finset.sum_eq_zero fun a _ => ?_
    have h := congrFun hc a
    simp only [Pi.zero_apply] at h
    rw [h, zero_smul]
  rw [← hy] at hHf hyw hwy hvdec
  rw [hvdec] at hHf hv ⊢
  simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC_add_left, ReciprocityTheory.ChartRestriction.G.FD.hermC_add_right, hyw, hwy,
    add_zero, zero_add] at hHf
  have hmaj : X.maj x τ (y + w) = (hermC τ.1 X.Gm y y).re - (hermC τ.1 X.Gm w w).re := by
    have h := congrArg Complex.re hHf
    simp at h
    linarith
  rw [hmaj]
  by_cases hw0 : w = 0
  · have hy0 : y ≠ 0 := by
      rw [hw0, add_zero] at hv
      exact hv
    have h2 : hermC τ.1 X.Gm w w = 0 := by
      rw [hw0]
      exact ReciprocityTheory.ChartRestriction.G.FD.hermC_zero_left _ _ _
    rw [h2, Complex.zero_re, sub_zero]
    exact hyy_pos hy0
  · have h1 := hneg w horth' hw0
    linarith
end ReciprocityTheory.ChartRestriction.G.FD.Data
