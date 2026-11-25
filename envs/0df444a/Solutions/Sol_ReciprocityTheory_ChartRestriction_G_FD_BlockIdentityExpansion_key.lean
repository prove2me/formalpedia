-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:12:33.388072+00:00
-- url     : https://prove2.me/submissions/46f9f41b-2725-4fd6-ad5f-e8756e33dba8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BlockIdentityExpansion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BlockIdentityExpansion_f_gram_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_selfadj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_ppos_sameFlag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_Pos_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_perp_kap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_perp_of_ppos_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_ppos_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_ppos_of_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_re_self_of_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_re_self_of_perp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_re_self_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
private lemma hermC_sum_left_lemma (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {m : ℕ} (c : Fin m → ℂ)
    (q : Fin m → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ k, c k • q k) v = ∑ k, c k * hermC τ G (q k) v := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ k, ∑ b, c k * q k a * τ (G a b) * conj (v b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, c k * q k a * τ (G a b) * conj (v b) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring
private lemma hermC_sum_right_lemma_2 (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {m : ℕ} (u : Fin r → ℂ)
    (d : Fin m → ℂ) (q : Fin m → Fin r → ℂ) :
    hermC τ G u (∑ l, d l • q l) = ∑ l, conj (d l) * hermC τ G u (q l) := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ l, ∑ b, u a * τ (G a b) * (conj (d l) * conj (q l b)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, u a * τ (G a b) * (conj (d l) * conj (q l b)) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring
private lemma hermC_add_left_fundamental_domains (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → ℂ) :
    hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := by
  unfold hermC
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
private lemma hermC_sub_left' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' v : Fin r → ℂ) :
    hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v := by
  unfold hermC
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
private lemma hermC_sub_right' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v v' : Fin r → ℂ) :
    hermC τ G u (v - v') = hermC τ G u v - hermC τ G u v' := by
  unfold hermC
  simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
private lemma hermC_smul_left_fundamental_domains (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ G (c • u) v = c * hermC τ G u v := by
  unfold hermC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
private lemma hermC_smul_right_fundamental_domains (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ G u (c • v) = conj c * hermC τ G u v := by
  unfold hermC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring
private lemma hermC_zero_left' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (v : Fin r → ℂ) :
    hermC τ G 0 v = 0 := by
  unfold hermC
  simp
private lemma hermC_zero_right' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u : Fin r → ℂ) :
    hermC τ G u 0 = 0 := by
  unfold hermC
  simp
private lemma ppos_smul_fundamental_domains (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (u : Fin r → ℂ) :
    X.ppos x τ (c • u) = c • X.ppos x τ u := by
  rw [Data.ppos_eq, Data.ppos_eq, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hermC_smul_left_fundamental_domains]
  ring
private lemma hermC_add_right_fundamental_domains (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v v' : Fin r → ℂ) :
    hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  unfold hermC
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
end
end ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion
theorem _root_.solution (X : DataX E r) (ξ : Fin r → E) (z0 x0 : Frame X.Ψ r)
    (f : X.Ψ → Fin (r - 2) → Fin r → ℂ) (h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (δ : ℝ)
    (hz : z0 ∈ X.dom) (hx0 : x0 ∈ X.dom) (hortho : X.IsOrtho x0)
    (hflag : X.SameFlag z0 x0) (hf : X.UBasis z0 ξ f)
    (hI : ∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
      X.lineV ξ s + X.Jz z0 (X.lineV ξ t))
    (hUz : ∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ)
    (hgraph : ∀ τ (v : Fin r → ℂ), v ∈ Submodule.span ℂ (f τ '' {k | (k : ℕ) < X.p0 - 1}) →
      ∀ c : Fin (r - 2) → ℂ, (h1 τ) *ᵥ v = ∑ k, c k • f τ k →
        (∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then 0 else ‖c k‖ ^ 2) ≤
          δ ^ 2 * ∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then ‖c k‖ ^ 2 else 0)
    (τ : X.Ψ) (v : Fin r → ℂ) (hv : v ∈ Spos X.toData z0 τ) :
    Neg X.toData x0 τ (h1 τ *ᵥ v) ≤ δ ^ 2 * Pos X.toData x0 τ (h1 τ *ᵥ v) := by
  classical
  obtain ⟨hperp, hJ, hgr, -, hspan⟩ := hf τ
  have hdet0 : (mat x0 τ).det ≠ 0 := (hx0 τ).1
  have hS : Spos X.toData z0 τ = Spos X.toData x0 τ := hflag τ
  have hJt : ∀ u, X.Jt z0 τ u = I • ((2 : ℂ) • X.ppos z0 τ u - u) := fun u => rfl

  have hPpos : ∀ k : Fin (r - 2), (k : ℕ) < X.p0 - 1 → X.ppos z0 τ (f τ k) = f τ k := by
    intro k hk
    have h := hJ k
    rw [if_pos hk, hJt] at h
    have h2 := smul_right_injective (Fin r → ℂ) Complex.I_ne_zero h
    have h3 : (2 : ℂ) • X.ppos z0 τ (f τ k) = (2 : ℂ) • f τ k := by
      rw [sub_eq_iff_eq_add.mp h2, two_smul]
    exact smul_right_injective (Fin r → ℂ) two_ne_zero h3
  have hPneg : ∀ k : Fin (r - 2), ¬ (k : ℕ) < X.p0 - 1 → X.ppos z0 τ (f τ k) = 0 := by
    intro k hk
    have h := hJ k
    rw [if_neg hk, hJt, neg_smul, ← smul_neg] at h
    have h2 := smul_right_injective (Fin r → ℂ) Complex.I_ne_zero h
    have h3 : (2 : ℂ) • X.ppos z0 τ (f τ k) = 0 := by
      have h4 := congrArg (· + f τ k) h2
      simpa using h4
    exact (smul_eq_zero.mp h3).resolve_left two_ne_zero
  have hfS : ∀ k : Fin (r - 2), (k : ℕ) < X.p0 - 1 → f τ k ∈ Spos X.toData z0 τ := by
    intro k hk
    rw [← hPpos k hk]
    exact ppos_mem (X := X.toData) z0 τ _
  have hvP : X.ppos z0 τ v = v := ppos_of_mem (X := X.toData) hz τ v hv
  have hvneg : ∀ k : Fin (r - 2), ¬ (k : ℕ) < X.p0 - 1 → hermC τ.1 X.Gm v (f τ k) = 0 := by
    intro k hk
    rw [← hvP, Data.ppos_selfadj (X := X.toData) hz τ v (f τ k), hPneg k hk, hermC_zero_right']

  obtain ⟨a, ha⟩ : ∃ a : Fin (r - 2) → ℂ,
      a = fun k : Fin (r - 2) => if (k : ℕ) < X.p0 - 1 then hermC τ.1 X.Gm v (f τ k) else 0 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin r → ℂ, w = ∑ k, a k • f τ k := ⟨_, rfl⟩
  have hwspan : w ∈ Submodule.span ℂ (f τ '' {k | (k : ℕ) < X.p0 - 1}) := by
    rw [hw]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : (k : ℕ) < X.p0 - 1
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    · simp [ha, hk]
  have hwS : w ∈ Spos X.toData z0 τ := by
    rw [hw]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : (k : ℕ) < X.p0 - 1
    · exact Submodule.smul_mem _ _ (hfS k hk)
    · simp [ha, hk]
  have hfw : ∀ k, hermC τ.1 X.Gm (f τ k) w =
      conj (a k) * (if (k : ℕ) < X.p0 - 1 then 1 else -1) := by
    intro k
    rw [hw, hermC_sum_right_lemma_2]
    simp only [hgr, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hfp : ∀ k, hermC τ.1 X.Gm (f τ k) (v - w) = 0 := by
    intro k
    rw [hermC_sub_right', hfw]
    by_cases hk : (k : ℕ) < X.p0 - 1
    · rw [if_pos hk, mul_one, ha]
      simp only [if_pos hk]
      rw [hermC_conj τ.1 X.Gm_herm, sub_self]
    · rw [if_neg hk, ha]
      simp only [if_neg hk, map_zero, zero_mul, sub_zero]
      rw [← hermC_conj τ.1 X.Gm_herm, hvneg k hk, map_zero]
  have hskew : ∀ u q, hermC τ.1 X.Gm (X.Jt z0 τ u) q = -hermC τ.1 X.Gm u (X.Jt z0 τ q) := by
    intro u q
    rw [hJt, hJt, hermC_smul_left_fundamental_domains, hermC_smul_right_fundamental_domains, hermC_sub_left', hermC_sub_right',
      hermC_smul_left_fundamental_domains, hermC_smul_right_fundamental_domains, Data.ppos_selfadj (X := X.toData) hz τ u q, Complex.conj_I]
    first
      | (simp only [map_ofNat]; ring)
      | (simp; ring)

  let Lq : (Fin r → ℂ) → (Fin r → ℂ) →ₗ[ℂ] ℂ := fun q =>
    { toFun := fun u => hermC τ.1 X.Gm u q
      map_add' := fun u u' => hermC_add_left_fundamental_domains _ _ u u' q
      map_smul' := fun c u => hermC_smul_left_fundamental_domains _ _ c u q }
  have hK : ⨅ i, LinearMap.ker (![Lq (Data.emb τ.1 ξ), Lq (X.Jt z0 τ (Data.emb τ.1 ξ))] i) ≤
      LinearMap.ker (Lq (v - w)) := by
    intro u hu
    rw [Submodule.mem_iInf] at hu
    have h0 : hermC τ.1 X.Gm u (Data.emb τ.1 ξ) = 0 := hu 0
    have h1' : hermC τ.1 X.Gm u (X.Jt z0 τ (Data.emb τ.1 ξ)) = 0 := hu 1
    have hJu : hermC τ.1 X.Gm (X.Jt z0 τ u) (Data.emb τ.1 ξ) = 0 := by rw [hskew, h1', neg_zero]
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hspan u h0 hJu)
    show hermC τ.1 X.Gm u (v - w) = 0
    rw [← hc, hermC_sum_left_lemma]
    exact Finset.sum_eq_zero fun k _ => by rw [hfp k, mul_zero]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (mem_span_of_iInf_ker_le_ker hK)
  have hc' : ∀ u, hermC τ.1 X.Gm u (v - w) =
      hermC τ.1 X.Gm u (conj (c 0) • Data.emb τ.1 ξ + conj (c 1) • X.Jt z0 τ (Data.emb τ.1 ξ)) := by
    intro u
    have h := LinearMap.congr_fun hc u
    simp only [Fin.sum_univ_two, LinearMap.add_apply, LinearMap.smul_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul] at h
    rw [hermC_add_right_fundamental_domains, hermC_smul_right_fundamental_domains, hermC_smul_right_fundamental_domains, Complex.conj_conj,
      Complex.conj_conj]
    exact h.symm
  have hnd : ∀ z : Fin r → ℂ, (∀ u, hermC τ.1 X.Gm u z = 0) → z = 0 := by
    intro z hz'
    rw [expand (X := X.toData) hortho τ hdet0 z]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [← hermC_conj τ.1 X.Gm_herm, hz', map_zero, mul_zero, zero_smul]
  have hpq : v - w = conj (c 0) • Data.emb τ.1 ξ + conj (c 1) • X.Jt z0 τ (Data.emb τ.1 ξ) := by
    refine sub_eq_zero.mp (hnd _ fun u => ?_)
    rw [hermC_sub_right', hc' u, sub_self]
  have hfix : h1 τ *ᵥ (v - w) = v - w := by
    have h := congrFun (hI (fun _ => conj (c 0)) (fun _ => conj (c 1))) τ
    simp only [Data.applyV, Data.lineV, Data.Jz, Pi.add_apply] at h
    have he : conj (c 0) • Data.emb τ.1 ξ + conj (c 1) • X.Jt z0 τ (Data.emb τ.1 ξ) =
        conj (c 0) • Data.emb τ.1 ξ + I • ((2 : ℂ) • X.ppos z0 τ (conj (c 1) • Data.emb τ.1 ξ) -
          conj (c 1) • Data.emb τ.1 ξ) := by
      rw [hJt, ppos_smul_fundamental_domains]
      first
        | module
        | (simp only [smul_sub, smul_smul]; ring_nf)
    rw [hpq, he]
    first
      | exact h
      | simpa using h

  have hwe : hermC τ.1 X.Gm w (Data.emb τ.1 ξ) = 0 := by
    rw [hw, hermC_sum_left_lemma]
    exact Finset.sum_eq_zero fun k _ => by rw [(hperp k).1, mul_zero]
  have hwP : X.ppos z0 τ w = w := ppos_of_mem (X := X.toData) hz τ w hwS
  have hp0 : ∀ τ' : X.Ψ, X.ppos z0 τ' 0 = 0 := fun τ' => by
    simpa using ppos_smul_fundamental_domains X.toData z0 τ' 0 0
  have hU : (fun τ' => if τ' = τ then w else 0) ∈ X.Uz z0 ξ := by
    refine ⟨fun τ' => ?_, fun τ' => ?_⟩
    · by_cases h : τ' = τ
      · simp only [if_pos h]
        rw [h]
        exact hwe
      · simp only [if_neg h]
        exact hermC_zero_left' _ _ _
    · by_cases h : τ' = τ
      · simp only [Data.Jz, if_pos h]
        rw [h, hwP, hermC_smul_left_fundamental_domains, hermC_sub_left', hermC_smul_left_fundamental_domains, hwe]
        ring
      · simp only [Data.Jz, if_neg h, hp0, smul_zero, sub_zero]
        exact hermC_zero_left' _ _ _
  have hA := hUz _ hU
  have hA1 : hermC τ.1 X.Gm (h1 τ *ᵥ w) (Data.emb τ.1 ξ) = 0 := by
    have h := hA.1 τ
    simpa [Data.applyV] using h
  have hA2 : hermC τ.1 X.Gm (X.Jt z0 τ (h1 τ *ᵥ w)) (Data.emb τ.1 ξ) = 0 := by
    have h := hA.2 τ
    simpa [Data.applyV, Data.Jz, Data.Jt] using h
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hspan _ hA1 hA2)
  have hg := hgraph τ w hwspan cc hcc.symm
  have hy : h1 τ *ᵥ v = (v - w) + ∑ k, cc k • f τ k := by
    rw [hcc]
    conv_rhs => rw [← hfix]
    rw [← Matrix.mulVec_add, sub_add_cancel]
  rw [hy]

  have hpS0 : v - w ∈ Spos X.toData x0 τ := hS ▸ Submodule.sub_mem _ hv hwS
  obtain ⟨b, hb⟩ : ∃ b : Fin (r - 2) → ℂ,
      b = fun k : Fin (r - 2) => if (k : ℕ) < X.p0 - 1 then 0 else cc k := ⟨_, rfl⟩
  have hNeq : PositiveSpanMatrices.Neg X.toData x0 τ ((v - w) + ∑ k, cc k • f τ k) =
      PositiveSpanMatrices.Neg X.toData x0 τ (∑ k, b k • f τ k) := by
    unfold PositiveSpanMatrices.Neg
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [hermC_add_left_fundamental_domains, perp_kap (X := X.toData) hortho τ _ hpS0 a', zero_add,
      hermC_sum_left_lemma, hermC_sum_left_lemma]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hb]
    by_cases hk : (k : ℕ) < X.p0 - 1
    · simp only [if_pos hk, zero_mul]
      rw [perp_kap (X := X.toData) hortho τ _ (hS ▸ hfS k hk) a', mul_zero]
    · simp only [if_neg hk]
  have hnegperp : ∀ b' : Fin X.p0,
      hermC τ.1 X.Gm (∑ k, b k • f τ k) (col (mat x0 τ) (Fin.castLE X.p0_le b')) = 0 := by
    intro b'
    rw [hermC_sum_left_lemma]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hb]
    by_cases hk : (k : ℕ) < X.p0 - 1
    · simp only [if_pos hk, zero_mul]
    · simp only [if_neg hk]
      rw [perp_of_ppos_zero (X := X.toData) hx0 τ (f τ k) ?_ b', mul_zero]
      rw [← FrameDegreeData.ppos_sameFlag (X := X.toData) hz hx0 hflag τ]
      exact hPneg k hk
  have hN : PositiveSpanMatrices.Neg X.toData x0 τ ((v - w) + ∑ k, cc k • f τ k) =
      ∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then 0 else ‖cc k‖ ^ 2 := by
    rw [hNeq]
    have h1' := re_self_of_perp (X := X.toData) hortho τ hdet0 _ hnegperp
    have h2' := f_gram_re X.toData ξ z0 f hf τ b
    have h3' : PositiveSpanMatrices.Neg X.toData x0 τ (∑ k, b k • f τ k) =
        -∑ k : Fin (r - 2), (if (k : ℕ) < X.p0 - 1 then ‖b k‖ ^ 2 else -‖b k‖ ^ 2) := by
      linarith
    rw [h3', ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hb]
    by_cases hk : (k : ℕ) < X.p0 - 1 <;> simp [hk]

  have hre := re_self_split (X := X.toData) hortho τ hdet0 ((v - w) + ∑ k, cc k • f τ k)
  have hpf : ∀ k, hermC τ.1 X.Gm (v - w) (f τ k) = 0 := fun k => by
    rw [← hermC_conj τ.1 X.Gm_herm, hfp k, map_zero]
  have hexp : (hermC τ.1 X.Gm ((v - w) + ∑ k, cc k • f τ k) ((v - w) + ∑ k, cc k • f τ k)).re =
      (hermC τ.1 X.Gm (v - w) (v - w)).re +
        (hermC τ.1 X.Gm (∑ k, cc k • f τ k) (∑ k, cc k • f τ k)).re := by
    rw [hermC_add_left_fundamental_domains, hermC_add_right_fundamental_domains, hermC_add_right_fundamental_domains,
      hermC_sum_right_lemma_2 τ.1 X.Gm (v - w), hermC_sum_left_lemma τ.1 X.Gm cc (f τ) (v - w)]
    simp only [hpf, hfp, mul_zero, Finset.sum_const_zero, add_zero, zero_add, Complex.add_re]
  have hSS := f_gram_re X.toData ξ z0 f hf τ cc
  have hPp := re_self_of_mem (X := X.toData) hortho τ hdet0 _ hpS0
  have hP0 := Pos_nonneg (X := X.toData) x0 τ (v - w)
  have hsplit : (∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then ‖cc k‖ ^ 2 else -‖cc k‖ ^ 2) =
      (∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then ‖cc k‖ ^ 2 else 0) -
        ∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then 0 else ‖cc k‖ ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  rw [hN] at hre ⊢
  have hmono : ∀ A B C : ℝ, C ≤ δ ^ 2 * A → A ≤ B → C ≤ δ ^ 2 * B := fun A B C h1 h2 =>
    h1.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg δ))
  refine hmono _ _ _ hg ?_
  linarith [hre, hexp, hSS, hPp, hP0, hsplit]
end ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion
