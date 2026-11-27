-- Prove2me | solution 1 for UpperTheory.nu_det_mul_sliceB_block_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:38:54.380799+00:00
-- url     : https://prove2.me/submissions/bc1000dd-085f-413e-908f-0fd33e55bcd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ScaledIntegerPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitThetaGridPathAvoidsOppositeCorner
import Definitions.Def_Development_AutomorphicArithmetic_DivisorFrames_NuDetMulSliceBBlockAction
import Theorems.Thm_GlobalTheory_SplitFlip_Assignment_read_mem_KO
import Theorems.Thm_GlobalTheory_SplitFlip_IsPath_eq_of_vertexDiff_eq
import Theorems.Thm_GlobalTheory_SplitFlip_IsPath_pairwise_vertexDiff
import Theorems.Thm_GlobalTheory_SplitFlip_apow_of_valuation_eq_one
import Theorems.Thm_GlobalTheory_SplitFlip_invT_inv_val
import Theorems.Thm_GlobalTheory_SplitFlip_invT_val
import Theorems.Thm_GlobalTheory_SplitFlip_valuation_gdet_of_mem_KO
import Theorems.Thm_GlobalTheory_SplitFlip_vertexDiff_tgt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise
private theorem not_touch_inner {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (hθ : Edge.theta i j ∈ γ)
    (hx : Edge.ex i j ∈ γ) {b : Edge} (hb : b ∈ γ) (h1 : b ≠ .theta i j) (h2 : b ≠ .ex i j) :
    b.src ≠ (i, j) ∧ b.tgt ≠ (i, j) := by
  refine ⟨fun hs => h2 (hγ.eq_of_vertexDiff_eq hb hx (by rw [hs])), fun ht => h1 ?_⟩
  have h3 := vertexDiff_tgt b
  have h4 := vertexDiff_tgt (.theta i j)
  rw [ht] at h3
  exact hγ.eq_of_vertexDiff_eq hb hθ (by simp only [Edge.tgt] at h4; omega)
private theorem nodup_of_isPath {γ : List Edge} (hγ : IsPath γ) : γ.Nodup :=
  hγ.pairwise_vertexDiff.imp fun {a b} h hab => by subst hab; exact lt_irrefl _ h
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise
namespace UpperTheory
theorem _root_.solution :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k} (ϖ : kˣ) (e : ℕ) (St : G.PiLocalization₂) (i j : ℕ), PassesThrough i j St.path → St.IsAdmissible .one ϖ e → ∀ u ∈ St.level (i, j), ∀ (x : G.Args) (Z : Matrix (Fin (G.rank (i, j))) (G.Cols i j) k), (G.nu i j (gdet u⁻¹) : ℂ) * G.sliceB i j St.tensor x (fromCols (u.valᵀ * Z.toCols₁) ((u⁻¹).val * Z.toCols₂)) = G.sliceB i j St.tensor x Z := by
  intro k _ _ _ _ G ϖ e St i j hpt hadm u hu x Z
  obtain ⟨γ, J, T⟩ := St
  obtain ⟨hpath, hlev, htens, hinv⟩ := hadm
  simp only at hpt hlev hpath htens hinv hu ⊢
  have hθ : Edge.theta i j ∈ γ := hpt.subset (by simp)
  have hx : Edge.ex i j ∈ γ := hpt.subset (by simp)
  have hnt := fun b hb h1 h2 => not_touch_inner (b := b) hpath hθ hx hb h1 h2
  have hnd := nodup_of_isPath hpath
  obtain ⟨l₁, l₂, hγ⟩ := hpt
  have hin : (i, j) ∈ innerVertices γ := by
    subst hγ
    refine List.mem_map.2 ⟨.ex i j, ?_, rfl⟩
    cases l₁ <;> simp
  have huK : u ∈ KO k _ := (hlev _ hin).2 hu
  have h := congrFun (hinv _ hin u hu)
    (Function.update (Function.update x (.theta i j) Z.toCols₁) (.ex i j) Z.toCols₂ᵀ)
  set g : G.VertexGroup := Pi.mulSingle (i, j) u with hg
  have hg0 : g (i, j) = u := Pi.mulSingle_eq_same _ _
  have hg1 : ∀ Y, Y ≠ (i, j) → g Y = 1 := fun Y hY => Pi.mulSingle_eq_of_ne hY _
  have hoff : ∀ b ∈ γ, b ≠ .theta i j → b ≠ .ex i j → G.edgeFactor .one g b = 1 := fun b hb h1 h2 => by
    simp [Grid.edgeFactor, hg1 _ (hnt b hb h1 h2).1, hg1 _ (hnt b hb h1 h2).2]
  have ha : ∀ z : ℂ, apow (gdet (Assignment.one.read u)) z = 1 := fun z =>
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO huK)) z
  have hsq : G.edgeFactor .one g (.theta i j) * G.edgeFactor .one g (.ex i j) = (G.nu i j (gdet u⁻¹) : ℂ) := by
    have e1 : g (i, j + 1) = 1 := hg1 _ (by simp)
    have e2 : g (i + 1, j) = 1 := hg1 _ (by simp)
    simp only [Grid.edgeFactor, Edge.src, Edge.tgt, hg0, e1, e2, ha, map_one, apow_one, mul_one]
    simp only [Grid.kappa, Grid.blockChar, Grid.nu, gdet, map_one, map_inv, MonoidHom.div_apply,
      Units.val_div_eq_div_val, Units.val_inv_eq_inv_val, Units.val_one, inv_one, mul_one, one_mul]
    field_simp
  have hprod : (γ.map (G.edgeFactor .one g)).prod = (G.nu i j (gdet u⁻¹) : ℂ) := by
    have p : ∀ l : List Edge, (∀ b ∈ l, b ∈ γ ∧ b ≠ .theta i j ∧ b ≠ .ex i j) →
        (l.map (G.edgeFactor .one g)).prod = 1 := fun l hl => List.prod_eq_one fun c hc => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
      exact hoff b (hl b hb).1 (hl b hb).2.1 (hl b hb).2.2
    subst hγ
    have q₁ := p l₁ fun b hb => ⟨by simp [hb], by
      rintro rfl; exact (List.nodup_append.1 (List.nodup_append.1 hnd).1).2.2 _ hb _ (by simp) rfl, by
      rintro rfl; exact (List.nodup_append.1 (List.nodup_append.1 hnd).1).2.2 _ hb _ (by simp) rfl⟩
    have q₂ := p l₂ fun b hb => ⟨by simp [hb], by
      rintro rfl; exact (List.nodup_append.1 hnd).2.2 _ (by simp) _ hb rfl, by
      rintro rfl; exact (List.nodup_append.1 hnd).2.2 _ (by simp) _ hb rfl⟩
    simp only [List.map_append, List.prod_append, q₁, q₂, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, one_mul, hsq]
  rw [Grid.pathAct, hprod] at h
  simp only [Grid.sliceB]
  rw [← h]
  congr 1
  refine htens.1 fun b hb => ?_
  have hne : Edge.theta i j ≠ Edge.ex i j := by simp
  by_cases hb2 : b = .ex i j
  · subst hb2
    simp only [Function.update_self, Grid.moveArgs, Assignment.read, invT_inv_val, hg0, invT_val]
    simp [hg1 (i + 1, j) (by simp), Matrix.transpose_mul]
  · by_cases hb1 : b = .theta i j
    · subst hb1
      simp only [Function.update_of_ne hne, Function.update_self, Grid.moveArgs, Assignment.read, invT_inv_val, hg0]
      simp [hg1 (i, j + 1) (by simp)]
    · simp [Grid.moveArgs, Function.update_of_ne hb1, Function.update_of_ne hb2,
        hg1 _ (hnt b hb hb1 hb2).1, hg1 _ (hnt b hb hb1 hb2).2]
end UpperTheory
