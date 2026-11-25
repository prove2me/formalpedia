-- Prove2me | solution 1 for P2M_UpperTheory_Comparison__charsA_aeb36eedc800
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:42.663815+00:00
-- url     : https://prove2.me/submissions/f00bdc69-4b1a-4e19-b7f1-bc7f3d7c2df8

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_PrimRead
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CardPsiA
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_TopsSum
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_charsA
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_dir_unit
import Theorems.Thm_Formalism_HC_HostRaw_isPrimOf_iff
import Theorems.Thm_Formalism_HC_HostRaw_isPrimOf_prim
import Theorems.Thm_Formalism_HC_HostRaw_kept_iff
import Theorems.Thm_Formalism_landauIteratedDerivatives_key
import Theorems.Thm_P2M_UpperTheory_Comparison__card_PsiA_f174cd9d4385
import Theorems.Thm_P2M_UpperTheory_Comparison__prim_read_a62b442f7a8d
import Theorems.Thm_P2M_UpperTheory_Comparison__tops_sum_c56a8a9dec6b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost
private theorem embedding_generator_eq (φ : Frame) (s : φ.A) : toE φ (φ.tau1 s) = Multiplicative.ofAdd ((0 : E0), s) := by
  first
  | rfl
  | simp [toE, Frame.tau1, Frame.iota, Frame.iotaInv, sgn2]
private theorem toE_iod (φ : Frame) : toE φ φ.iod = Multiplicative.ofAdd (sgc0 : E0 × φ.A) := by
  rfl
private theorem chr_coe_eq_addChar_toE (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) (g : φ.GG) :
    ((chr φ ψ g : ℂˣ) : ℂ) = ψ (Multiplicative.toAdd (toE φ g)) := rfl
private theorem mem_PsiA_iff (φ : Frame) (ψ : AddChar (E0 × φ.A) ℂ) : ψ ∈ PsiA φ.A0 ↔ Frame.TrivialOnFirstFactor (chr φ ψ) := by
  have key : ∀ s : φ.A, ((chr φ ψ (φ.tau1 s) : ℂˣ) : ℂ) = ψ ((0 : E0), s) := by
    intro s
    rw [chr_coe_eq_addChar_toE, embedding_generator_eq]
    rfl
  simp only [PsiA, Frame.TrivialOnFirstFactor, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h s hs
    apply Units.ext
    rw [Units.val_one, key]
    exact h s hs
  · intro h s hs
    have h2 := congrArg Units.val (h s hs)
    rw [key, Units.val_one] at h2
    exact h2
private theorem mem_keptA (Λ : Level) (φ : Frame) (H : HostRaw φ) (ψ : AddChar (E0 × φ.A) ℂ) :
    ψ ∈ keptA Λ H ↔ H.Kept Λ.KEPT (chr φ ψ) := by
  simp [keptA]
private theorem chr_bounded (Λ : Level) (φ : Frame) (H : HostRaw φ) (ψ : AddChar (E0 × φ.A) ℂ) (h : ψ ∈ PsiA φ.A0)
    (hk : ψ ∉ keptA Λ H) : chr φ ψ ∈ H.Bounded Λ.KEPT := by
  have h1 := (mem_PsiA_iff φ ψ).1 h
  have h2 : ¬ H.Kept Λ.KEPT (chr φ ψ) := fun h => hk ((mem_keptA Λ φ H ψ).2 h)
  have h3 : φ.iod * φ.iod = 1 := by
    simp [Frame.iod]
  have h4 : chr φ ψ φ.iod * chr φ ψ φ.iod = 1 := by rw [← map_mul, h3, map_one]
  have h5 : ((chr φ ψ φ.iod : ℂˣ) : ℂ) * ((chr φ ψ φ.iod : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, h4, Units.val_one]
  rcases mul_self_eq_one_iff.1 h5 with h6 | h6
  · exact Or.inl ⟨⟨h1, Units.ext h6⟩, h2⟩
  · exact Or.inr ⟨h1, Units.ext h6⟩
private theorem eq_of_prim_eq (φ : Frame) (H : HostAx φ) (θ θ' : φ.Char)
    (h : H.toHostRaw.prim θ = H.toHostRaw.prim θ') : θ = θ' := by
  apply MonoidHom.ext
  intro g
  obtain ⟨u, rfl⟩ := HostDer.art_surj H.der g
  have h1 := (H.toHostRaw.isPrimOf_prim θ).2
  have h2 := (H.toHostRaw.isPrimOf_prim θ').2
  rw [← h] at h2
  have hc := ZMod.val_coe_unit_coprime u
  have e := (h1 _ hc).symm.trans (h2 _ hc)
  apply Units.ext
  rw [← HostRaw.dir_unit, ← HostRaw.dir_unit]
  simpa [HostRaw.dirAt, ZMod.natCast_zmod_val] using e
private theorem zero_kept (Λ : Level) (φ : Frame) (H : HostRaw φ) : (0 : AddChar (E0 × φ.A) ℂ) ∈ keptA Λ H := by
  rw [mem_keptA, HostRaw.kept_iff]
  have hc : chr φ 0 = 1 := by
    refine MonoidHom.ext fun g => Units.ext ?_
    rw [chr_coe_eq_addChar_toE, MonoidHom.one_apply, Units.val_one, AddChar.zero_apply]
  have hd : H.dir 1 = 1 := by
    apply MulChar.ext
    intro u
    rw [HostRaw.dir_unit]
    simp
  rw [hc, HostRaw.prim, hd, PChar.of_one]
  exact Λ.one_mem
end

set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost
namespace UpperTheory.Comparison₂
theorem _root_.solution :
    ∀ (Λ : Level) (φ : Frame) (H : HostAx φ) (TT : Finset φ.A) (x eps C : ℝ) (ell : AddChar (E0 × φ.A) ℂ → ℂ), 0 < x →
      EAtH Λ H.toHostRaw TT x eps C → HostAddCharCompatible H.toHostRaw ell →
        CharsA ell φ.A0 (keptA Λ H.toHostRaw) TT (3 * (Λ.o : ℝ) + 1)⁻¹ (4 * (Λ.o : ℝ)) (koOf Λ) C eps x := by
  intro Λ φ H TT x eps C ell hx hE hL
  have ho := hE.o_eq
  have kept_xp : ∀ ψ ∈ keptA Λ H.toHostRaw, chr φ ψ ∈ φ.Xp := by
    intro ψ hψ
    obtain ⟨p, hp, hpp⟩ := (mem_keptA Λ φ H.toHostRaw ψ).1 hψ
    obtain ⟨θ, hθ, hθp⟩ := hE.kept p hp
    have e1 := (H.toHostRaw.isPrimOf_iff _ _).1 hpp
    have e2 := (H.toHostRaw.isPrimOf_iff _ _).1 hθp
    have hq : chr φ ψ = θ := eq_of_prim_eq φ H _ _ (e1.symm.trans e2)
    rw [hq]
    exact hθ
  refine ⟨zero_kept Λ φ H.toHostRaw, ?_, ?_, ?_, ?_, ?_⟩
  · intro ψ hψ
    have hX := kept_xp ψ hψ
    refine ⟨(mem_PsiA_iff φ ψ).2 hX.1, ?_⟩
    have h2 := congrArg Units.val hX.2
    rw [chr_coe_eq_addChar_toE, toE_iod, Units.val_one] at h2
    exact h2
  · rw [card_PsiA, ho]
    push_cast
    exact le_refl _
  · intro ψ hψ hnt
    have hP := (mem_PsiA_iff φ ψ).2 (kept_xp ψ hψ).1
    have hb := tops_sum φ TT _ hE.shares ψ hP hnt
    rw [ho] at hb
    refine hb.trans ?_
    have hδ : 0 ≤ x ^ (-1 + eps) := Real.rpow_nonneg hx.le _
    have h3 : 0 ≤ 3 * (Λ.o : ℝ) * x ^ (-1 + eps) * (TT.card : ℝ) := by positivity
    linarith
  · intro ψ hψ hne
    rw [(prim_read φ H ell hL ψ).1 hne, koOf]
    have hm : H.toHostRaw.prim (chr φ ψ) ∈ Λ.KEPT :=
      (HostRaw.kept_iff _ _ _).1 ((mem_keptA Λ φ H.toHostRaw ψ).1 hψ)
    exact Finset.single_le_sum (f := fun p : PChar => ‖An.logDerivativeAtOne p.χ‖) (fun _ _ => norm_nonneg _) hm
  · intro ψ hP hk
    have hne : ψ ≠ 0 := by
      rintro rfl
      exact hk (zero_kept Λ φ H.toHostRaw)
    rw [(prim_read φ H ell hL ψ).1 hne]
    have hb := chr_bounded Λ φ H.toHostRaw ψ hP hk
    haveI := (H.toHostRaw.prim (chr φ ψ)).ne
    exact hE.bdL _ hb _ _ (H.toHostRaw.isPrimOf_prim _)
end UpperTheory.Comparison₂
