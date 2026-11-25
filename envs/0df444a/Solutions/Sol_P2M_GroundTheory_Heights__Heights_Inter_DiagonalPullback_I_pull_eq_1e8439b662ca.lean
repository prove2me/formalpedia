-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_I_pull_eq_1e8439b662ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:16:34.018812+00:00
-- url     : https://prove2.me/submissions/719a6be9-a26c-405a-864a-46cc39ce6fe9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPullI
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_pullDeg_eq_alt_cab5d464467e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_X_mem_diag_iff_cd110d0e6e0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_cycR_eq_finsum_b745b6d310f8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_isSmoothHerm_pull_c9953dbb0544
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_ptsIntegral_congr_mcPts_6069163e8079
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I2_recR_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 DiagRAux
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagonalPullback
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalPullback
theorem _root_.solution {D : ℕ} (S : ProjectiveLineBundle D)
    (I : Ideal (MRing S.WIdx) → (n : ℕ) → (Fin n → HermLine S.WIdx) → ℝ) (hF : IsIntersectionFamily I)
    (hΔ : IsArithVar S.Diag (D + 1)) (hDP : T.DiagPullStatement (Φ := S.Φ) S.x S.δ S.e S.φ)
    (L : Fin D → HermLine S.WIdx) (hL : ∀ j, IsSmoothHerm (L j))
    (A : HermLine S.YIdx) (A₀ A₁ : HermLine S.WIdx) (d : T.YBlk → ℕ) (hd : ∀ k, A.a k = d k)
    (hA : IsSmoothHerm A) (hp0 : IsPullHerm (diagonalBlockIndex 0) (T.yyEmb 0) A A₀)
    (hp1 : IsPullHerm (diagonalBlockIndex 1) (T.yyEmb 1) A A₁) :
    I S.Diag (D + 1) (Fin.snoc L A₀) = I S.Diag (D + 1) (Fin.snoc L A₁) := by
  have hprime : S.Diag.IsPrime := hΔ.2.1.1
  have hrel : IsRelevant S.Diag := hΔ.2.1.2.2
  obtain ⟨ib, hib⟩ := hrel .base
  obtain ⟨il, hil⟩ := hrel .det
  obtain ⟨ik, hik⟩ := hrel .line0
  have hik' : (X ⟨T.WBlk.line1, (ik : S.κ)⟩ : MRing S.WIdx) ∉ S.Diag := by
    intro h
    apply hik
    rw [X_mem_diag_iff] at h ⊢
    exact h

  set s : MRing S.YIdx := X ⟨T.YBlk.base, (ib : S.ι)⟩ ^ d .base * X ⟨T.YBlk.det, (il : S.ν)⟩ ^ d .det *
    X ⟨T.YBlk.line, (ik : S.κ)⟩ ^ d .line with hs_def
  have hs : IsMultiHomog s d := by
    have h := exHomog_mul (exHomog_mul (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base ib) (d .base))
      (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.det il) (d .det)))
      (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.line ik) (d .line))
    convert h using 1
    funext k
    cases k <;> simp
  have hs0 : rename (T.yyEmb 0) s = X ⟨T.WBlk.base, ib⟩ ^ d .base * X ⟨T.WBlk.det, il⟩ ^ d .det *
      X ⟨T.WBlk.line0, ik⟩ ^ d .line := by
    simp only [hs_def, map_mul, map_pow, rename_X]
    rfl
  have hs1 : rename (T.yyEmb 1) s = X ⟨T.WBlk.base, ib⟩ ^ d .base * X ⟨T.WBlk.det, il⟩ ^ d .det *
      X ⟨T.WBlk.line1, (ik : S.κ)⟩ ^ d .line := by
    simp only [hs_def, map_mul, map_pow, rename_X]
    rfl
  have hpow : ∀ {f : MRing S.WIdx} (n : ℕ), f ∉ S.Diag → f ^ n ∉ S.Diag :=
    fun n hf h => hf (hprime.mem_of_pow_mem n h)
  have hmul : ∀ {f g : MRing S.WIdx}, f ∉ S.Diag → g ∉ S.Diag → f * g ∉ S.Diag :=
    fun hf hg h => (hprime.mem_or_mem h).elim hf hg
  have hn0 : rename (T.yyEmb 0) s ∉ S.Diag := by
    rw [hs0]
    exact hmul (hmul (hpow _ hib) (hpow _ hil)) (hpow _ hik)
  have hn1 : rename (T.yyEmb 1) s ∉ S.Diag := by
    rw [hs1]
    exact hmul (hmul (hpow _ hib) (hpow _ hil)) (hpow _ hik')

  set a0 : T.WBlk → ℕ := d .base • Pi.single T.WBlk.base 1 + d .det • Pi.single T.WBlk.det 1 +
    d .line • Pi.single T.WBlk.line0 1 with ha0
  set a1 : T.WBlk → ℕ := d .base • Pi.single T.WBlk.base 1 + d .det • Pi.single T.WBlk.det 1 +
    d .line • Pi.single T.WBlk.line1 1 with ha1
  have hh0 : IsMultiHomog (rename (T.yyEmb 0) s) a0 := by
    rw [hs0]
    exact exHomog_mul (exHomog_mul (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base ib) _)
      (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.det il) _)) (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.line0 ik) _)
  have hh1 : IsMultiHomog (rename (T.yyEmb 1) s) a1 := by
    rw [hs1]
    exact exHomog_mul (exHomog_mul (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base ib) _)
      (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.det il) _))
      (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.line1 (ik : S.κ)) _)
  have hT0 : A₀.a = T.pullDeg 0 A.a := by rw [hp0.1, pullDeg_eq_alt]
  have hT1 : A₁.a = T.pullDeg 1 A.a := by rw [hp1.1, pullDeg_eq_alt]
  have hd0 : ∀ k, A₀.a k = a0 k := by
    intro k
    rw [hT0]
    cases k <;> simp [T.pullDeg, ha0, hd]
  have hd1 : ∀ k, A₁.a k = a1 k := by
    intro k
    rw [hT1]
    cases k <;> simp [T.pullDeg, ha1, hd]

  have e0 := hF.2.2 S.Diag D L A₀ _ a0 hΔ hL (isSmoothHerm_pull 0 hA hp0) hd0 hh0 hn0
  have e1 := hF.2.2 S.Diag D L A₁ _ a1 hΔ hL (isSmoothHerm_pull 1 hA hp1) hd1 hh1 hn1
  rw [e0, e1, recR_eq, recR_eq, cycR_eq_finsum, cycR_eq_finsum, (hDP (S.a 0)).1 s d hs]
  congr 1
  exact ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) fun z hz =>
    (hDP (S.a 0)).2.2 s d hs A A₀ A₁ hd ⟨hT0, hp0.2⟩ ⟨hT1, hp1.2⟩ z hz
end GroundTheory.Heights₂.Heights.Inter.DiagonalPullback
