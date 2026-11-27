-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:21:39.720984+00:00
-- url     : https://prove2.me/submissions/715059ef-ab1e-49c0-97e7-661aa761f955

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PBlocksAlg
import Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_BlockAlgebra_piece

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] (r s : ℕ)
    (A B : ι → ℕ → Module.End ℂ V) (m : ι → Multiset ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hAW : ∀ i k, ∀ w ∈ W, A i k w ∈ W) (hBW : ∀ i k, ∀ w ∈ W, B i k w ∈ W)
    (hAA : ∀ i k j l, ∀ w ∈ W, A i k (A j l w) = A j l (A i k w))
    (hAB : ∀ i k j l, ∀ w ∈ W, A i k (B j l w) = B j l (A i k w))
    (hBB : ∀ i k j l, ∀ w ∈ W, B i k (B j l w) = B j l (B i k w))
    (hA1 : ∀ i, ∀ w ∈ W, A i r w = w) (hB1 : ∀ i, ∀ w ∈ W, B i s w = w)
    (hm : ∀ i, (m i).Nodup) (v : V) (hv : v ∈ W)
    (hrel : ∀ i (u : ℂ), (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) ((∑ l ∈ Finset.range (s + 1), u ^ l • B i l) v) =
      ((m i).map (u + ·)).prod • v) :
    ∃ (S : Finset (ι → Multiset ℂ)) (x : (ι → Multiset ℂ) → V), (∀ σ ∈ S, x σ ∈ W) ∧ v = ∑ σ ∈ S, x σ ∧
      ∀ σ ∈ S, ∀ i, σ i ≤ m i ∧ Multiset.card (σ i) = r ∧ ∀ u : ℂ,
        (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) (x σ) = ((σ i).map (u + ·)).prod • x σ ∧
        (∑ l ∈ Finset.range (s + 1), u ^ l • B i l) (x σ) = ((m i - σ i).map (u + ·)).prod • x σ := by
  classical

  let A' : ι → ℕ → Module.End ℂ W := fun i k => (A i k).restrict (fun w hw => hAW i k w hw)
  let B' : ι → ℕ → Module.End ℂ W := fun i k => (B i k).restrict (fun w hw => hBW i k w hw)
  have cAA : ∀ i k j l, Commute (A' i k) (A' j l) := fun i k j l =>
    LinearMap.ext fun w => Subtype.ext (hAA i k j l w.1 w.2)
  have cAB : ∀ i k j l, Commute (A' i k) (B' j l) := fun i k j l =>
    LinearMap.ext fun w => Subtype.ext (hAB i k j l w.1 w.2)
  have cBB : ∀ i k j l, Commute (B' i k) (B' j l) := fun i k j l =>
    LinearMap.ext fun w => Subtype.ext (hBB i k j l w.1 w.2)
  let Gs : Set (Module.End ℂ W) :=
    Set.range (fun p : ι × ℕ => A' p.1 p.2) ∪ Set.range (fun p : ι × ℕ => B' p.1 p.2)
  have hGs : ∀ x ∈ Gs, ∀ y ∈ Gs, Commute x y := by
    rintro _ (⟨⟨i, k⟩, rfl⟩ | ⟨⟨i, k⟩, rfl⟩) _ (⟨⟨j, l⟩, rfl⟩ | ⟨⟨j, l⟩, rfl⟩)
    · exact cAA i k j l
    · exact cAB i k j l
    · exact (cAB j l i k).symm
    · exact cBB i k j l
  let R := Algebra.adjoin ℂ Gs
  have hRc : ∀ x ∈ R, ∀ y ∈ R, Commute x y := fun x hx y hy =>
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb =>
      (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun c hc => hGs b hb c hc).symm
  have hAR : ∀ i k, A' i k ∈ R := fun i k => Algebra.subset_adjoin (Or.inl ⟨(i, k), rfl⟩)
  have hBR : ∀ i k, B' i k ∈ R := fun i k => Algebra.subset_adjoin (Or.inr ⟨(i, k), rfl⟩)
  let Cop : ι → ℂ → Module.End ℂ W := fun i u => ∑ k ∈ Finset.range (r + 1), u ^ k • A' i k
  let Dop : ι → ℂ → Module.End ℂ W := fun i u => ∑ l ∈ Finset.range (s + 1), u ^ l • B' i l
  have hCR : ∀ i u, Cop i u ∈ R := fun i u => R.sum_mem fun k _ => R.smul_mem (hAR i k) _
  have hDR : ∀ i u, Dop i u ∈ R := fun i u => R.sum_mem fun k _ => R.smul_mem (hBR i k) _
  have hCv : ∀ i u (w : W), ((Cop i u w : W) : V) = (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) w := by
    intro i u w
    simp [Cop, A', LinearMap.sum_apply, Submodule.coe_sum]
  have hDv : ∀ i u (w : W), ((Dop i u w : W) : V) = (∑ l ∈ Finset.range (s + 1), u ^ l • B i l) w := by
    intro i u w
    simp [Dop, B', LinearMap.sum_apply, Submodule.coe_sum]

  let v' : W := ⟨v, hv⟩
  let W' : Submodule ℂ W := (Subalgebra.toSubmodule R).map (LinearMap.applyₗ v')
  have hW'm : ∀ w, w ∈ W' ↔ ∃ a ∈ R, a v' = w := fun w => Submodule.mem_map.trans Iff.rfl
  have hW'inv : ∀ x ∈ R, ∀ w ∈ W', x w ∈ W' := by
    intro x hx w hw
    obtain ⟨a, ha, rfl⟩ := (hW'm w).1 hw
    exact (hW'm _).2 ⟨x * a, R.mul_mem hx ha, rfl⟩
  have hrelv : ∀ i u, Cop i u (Dop i u v') = ((m i).map (u + ·)).prod • v' := fun i u =>
    Subtype.ext (by rw [hCv, hDv]; exact hrel i u)
  have hrelW' : ∀ i u, ∀ w ∈ W', Cop i u (Dop i u w) = ((m i).map (u + ·)).prod • w := by
    intro i u w hw
    obtain ⟨a, ha, rfl⟩ := (hW'm w).1 hw
    have e1 : Dop i u (a v') = a (Dop i u v') := by
      rw [← Module.End.mul_apply, (hRc _ (hDR i u) _ ha).eq, Module.End.mul_apply]
    have e2 : Cop i u (a (Dop i u v')) = a (Cop i u (Dop i u v')) := by
      rw [← Module.End.mul_apply, (hRc _ (hCR i u) _ ha).eq, Module.End.mul_apply]
    rw [e1, e2, hrelv, map_smul]

  let f : (ι × ℕ) ⊕ (ι × ℕ) → Module.End ℂ W' := Sum.elim
    (fun p => (A' p.1 p.2).restrict (fun w hw => hW'inv _ (hAR p.1 p.2) w hw))
    (fun p => (B' p.1 p.2).restrict (fun w hw => hW'inv _ (hBR p.1 p.2) w hw))
  have hfR : ∀ j, ∃ x ∈ R, ∀ w : W', (f j w : W) = x w := by
    rintro (⟨i, k⟩ | ⟨i, k⟩)
    · exact ⟨A' i k, hAR i k, fun w => rfl⟩
    · exact ⟨B' i k, hBR i k, fun w => rfl⟩
  have hfc : ∀ j j', Commute (f j) (f j') := by
    intro j j'
    obtain ⟨x, hx, hxe⟩ := hfR j
    obtain ⟨y, hy, hye⟩ := hfR j'
    refine LinearMap.ext fun w => Subtype.ext ?_
    change (f j (f j' w) : W) = (f j' (f j w) : W)
    rw [hxe, hye, hye, hxe, ← Module.End.mul_apply, (hRc x hx y hy).eq, Module.End.mul_apply]
  have hT := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun j j' _ => hfc j j') (fun j => Module.End.iSup_maxGenEigenspace_eq_top _)
  let v'' : W' := ⟨v', (hW'm v').2 ⟨1, R.one_mem, rfl⟩⟩
  have hv'' : v'' ∈ ⨆ χ : (ι × ℕ) ⊕ (ι × ℕ) → ℂ, ⨅ j, (f j).maxGenEigenspace (χ j) := by
    rw [hT]; exact Submodule.mem_top
  obtain ⟨Fs, hFs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hv''
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).1 hFs
  let P : ((ι × ℕ) ⊕ (ι × ℕ) → ℂ) → Submodule ℂ W' := fun χ => ⨅ j, (f j).maxGenEigenspace (χ j)
  have hPf : ∀ χ j, ∀ x ∈ P χ, f j x ∈ P χ := by
    intro χ j x hx
    simp only [P, Submodule.mem_iInf] at hx ⊢
    intro j'
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hfc j' j) (χ j') (hx j')
  let xx : ((ι × ℕ) ⊕ (ι × ℕ) → ℂ) → V := fun χ => (((μ χ : W') : W) : V)
  have key : ∀ χ : (ι × ℕ) ⊕ (ι × ℕ) → ℂ, ∃ σ : ι → Multiset ℂ, (μ χ : W') ≠ 0 → ∀ i, σ i ≤ m i ∧
      Multiset.card (σ i) = r ∧ ∀ u : ℂ,
        (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) (xx χ) = ((σ i).map (u + ·)).prod • xx χ ∧
        (∑ l ∈ Finset.range (s + 1), u ^ l • B i l) (xx χ) = ((m i - σ i).map (u + ·)).prod • xx χ := by
    intro χ
    by_cases h0 : (μ χ : W') = 0
    · exact ⟨fun _ => 0, fun h => absurd h0 h⟩
    have hpc : ∀ i, ∃ σi : Multiset ℂ, σi ≤ m i ∧ Multiset.card σi = r ∧ ∀ u : ℂ,
        (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) (xx χ) = (σi.map (u + ·)).prod • xx χ ∧
        (∑ l ∈ Finset.range (s + 1), u ^ l • B i l) (xx χ) = ((m i - σi).map (u + ·)).prod • xx χ := by
      intro i
      have : Nontrivial (P χ) := ⟨⟨μ χ, 0, fun h => h0 (congrArg Subtype.val h)⟩⟩
      let a : ℕ → Module.End ℂ (P χ) := fun k => (f (Sum.inl (i, k))).restrict (hPf χ _)
      let b : ℕ → Module.End ℂ (P χ) := fun l => (f (Sum.inr (i, l))).restrict (hPf χ _)
      have hcr : ∀ j j', Commute ((f j).restrict (hPf χ j)) ((f j').restrict (hPf χ j')) := fun j j' =>
        LinearMap.ext fun w => Subtype.ext (LinearMap.congr_fun (hfc j j').eq w.1)
      have ha : a r = 1 := LinearMap.ext fun w => Subtype.ext (Subtype.ext (Subtype.ext (hA1 i _ w.1.1.2)))
      have hb : b s = 1 := LinearMap.ext fun w => Subtype.ext (Subtype.ext (Subtype.ext (hB1 i _ w.1.1.2)))
      have hval : ∀ u (w : P χ), ((((∑ k ∈ Finset.range (r + 1), u ^ k • a k) w : P χ) : W') : W) = Cop i u w := by
        intro u w
        simp [a, f, Cop, LinearMap.sum_apply, Submodule.coe_sum]
      have hvalD : ∀ u (w : P χ), ((((∑ l ∈ Finset.range (s + 1), u ^ l • b l) w : P χ) : W') : W) = Dop i u w := by
        intro u w
        simp [b, f, Dop, LinearMap.sum_apply, Submodule.coe_sum]
      have hrelP : ∀ u : ℂ, (∑ k ∈ Finset.range (r + 1), u ^ k • a k) * (∑ l ∈ Finset.range (s + 1), u ^ l • b l) =
          ((m i).map (u + ·)).prod • (1 : Module.End ℂ (P χ)) := by
        intro u
        refine LinearMap.ext fun w => Subtype.ext (Subtype.ext ?_)
        rw [Module.End.mul_apply, hval]
        have e : ((((∑ l ∈ Finset.range (s + 1), u ^ l • b l) w : P χ) : W')) =
            ⟨Dop i u w, hW'inv _ (hDR i u) _ w.1.2⟩ := Subtype.ext (hvalD u w)
        rw [e]
        change Cop i u (Dop i u w.1.1) = _
        rw [hrelW' i u _ w.1.2]
        rfl
      have hnil : ∀ j, IsNilpotent ((f j).restrict (hPf χ j) - χ j • 1) := by
        intro j
        have h1 := Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (f j) (χ j)
        have hp : Set.MapsTo (f j - algebraMap ℂ (Module.End ℂ W') (χ j)) (P χ) (P χ) := fun x hx => by
          simp only [LinearMap.sub_apply, Module.algebraMap_end_apply]
          exact (P χ).sub_mem (hPf χ j x hx) ((P χ).smul_mem _ hx)
        have e : (f j).restrict (hPf χ j) - χ j • 1 = (f j - algebraMap ℂ (Module.End ℂ W') (χ j)).restrict hp := by
          refine LinearMap.ext fun w => Subtype.ext ?_
          rfl
        rw [e]
        exact Module.End.isNilpotent_restrict_of_le (hp := hp) (iInf_le _ j) h1
      obtain ⟨σi, h1, h2, h3⟩ := piece r s a b (fun k l => hcr _ _) (fun k l => hcr _ _) (fun k l => hcr _ _) ha hb
        (m i) (hm i) hrelP (fun k => χ (Sum.inl (i, k))) (fun l => χ (Sum.inr (i, l))) (fun k => hnil _)
        (fun l => hnil _)
      refine ⟨σi, h1, h2, fun u => ⟨?_, ?_⟩⟩
      · have e := congrArg (fun T : Module.End ℂ (P χ) => ((((T (μ χ) : P χ) : W') : W) : V)) (h3 u).1
        rw [hval, hCv] at e
        rw [e]
        rfl
      · have e := congrArg (fun T : Module.End ℂ (P χ) => ((((T (μ χ) : P χ) : W') : W) : V)) (h3 u).2
        rw [hvalD, hDv] at e
        rw [e]
        rfl
    choose σ hσ using hpc
    exact ⟨σ, fun _ i => hσ i⟩
  choose sig hsig using key
  set Fs' := Fs.filter (fun χ => (μ χ : W') ≠ 0) with hFs'
  refine ⟨Fs'.image sig, fun σ => ∑ χ ∈ Fs'.filter (fun χ => sig χ = σ), xx χ, ?_, ?_, ?_⟩
  · intro σ _
    exact W.sum_mem fun χ _ => ((μ χ : W') : W).2
  · rw [Finset.sum_fiberwise_of_maps_to (fun χ hχ => Finset.mem_image_of_mem sig hχ)]
    have e1 : v = (((v'' : W') : W) : V) := rfl
    rw [e1, ← hμ, Submodule.coe_sum, Submodule.coe_sum, hFs', Finset.sum_filter]
    refine Finset.sum_congr rfl fun χ _ => ?_
    split_ifs with h
    · rfl
    · rw [not_not] at h
      simp [h]
  · rintro σ hσ i
    obtain ⟨χ₀, hχ₀, rfl⟩ := Finset.mem_image.1 hσ
    obtain ⟨h1, h2, -⟩ := hsig χ₀ (Finset.mem_filter.1 hχ₀).2 i
    refine ⟨h1, h2, fun u => ⟨?_, ?_⟩⟩
    · rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      obtain ⟨hχF, hχe⟩ := Finset.mem_filter.1 hχ
      rw [← hχe]
      exact ((hsig χ (Finset.mem_filter.1 hχF).2 i).2.2 u).1
    · rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      obtain ⟨hχF, hχe⟩ := Finset.mem_filter.1 hχ
      rw [← hχe]
      exact ((hsig χ (Finset.mem_filter.1 hχF).2 i).2.2 u).2
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
