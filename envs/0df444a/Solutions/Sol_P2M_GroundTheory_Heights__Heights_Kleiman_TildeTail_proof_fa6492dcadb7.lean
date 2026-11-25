-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TildeTail_proof_fa6492dcadb7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:46:46.378607+00:00
-- url     : https://prove2.me/submissions/a76e7860-f64e-4d3f-bc80-73f66103d6fe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cocycle_eq_coneSingle_d0d23a2f80fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_exists_cocycle_of_mem_secs_a6b4983c8a3e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_coneSub_finite_e7769f5bc1e6


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace TildeTail
theorem _root_.solution (h : SerreTail.Statement.{u, w}) : TildeTail.Statement.{u, w} := by
  classical
  intro S _ _ Ω _ _ N x M hx c₁
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hx (funext hne)
  let K₀ : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
    ⟨⟨{i₀}, Finset.singleton_nonempty i₀, Finset.subset_univ _⟩, Finset.card_singleton i₀⟩
  have hK₀ : K₀.1.1 ⊆ support x := Finset.singleton_subset_iff.mpr ((mem_support x).mpr hi₀)

  let Ψ : Cech.Cochain (locSys S N M.coneSub) 0 →ₗ[Poly S N] ConeLaurent S x :=
    (M.cellCone K₀.1).comp (LinearMap.proj (R := Poly S N)
      (φ := fun K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 => LocMod S N M.coneSub K.1.1) K₀)
  have hΨ : ∀ z, Ψ z = M.cellCone K₀.1 (z K₀) := fun z => rfl
  obtain ⟨t, ht, hspan⟩ := h S N M.coneSub M.coneGraded M.coneSub_finite c₁

  let G : Submodule S (Cech.Cochain (locSys S N M.coneSub) 0) :=
    { carrier := {z | ∀ d, coeffAt S x d (Ψ z) ∈ (M.tildeSys d).secs ∧ (d < c₁ → coeffAt S x d (Ψ z) = 0)}
      add_mem' := fun {a b} ha hb d => by
        rw [map_add, map_add]
        exact ⟨add_mem (ha d).1 (hb d).1, fun hd => by rw [(ha d).2 hd, (hb d).2 hd, add_zero]⟩
      zero_mem' := fun d => by rw [map_zero, map_zero]; exact ⟨zero_mem _, fun _ => rfl⟩
      smul_mem' := fun s z hz d => by
        rw [LinearMap.map_smul_of_tower, map_smul]
        exact ⟨Submodule.smul_mem _ s (hz d).1, fun hd => by rw [(hz d).2 hd, smul_zero]⟩ }
  have hG : H0tail M.coneGraded c₁ ≤ G := by
    refine iSup₂_le fun c hc z hz => ?_
    show ∀ d, coeffAt S x d (Ψ z) ∈ (M.tildeSys d).secs ∧ (d < c₁ → coeffAt S x d (Ψ z) = 0)
    intro d
    obtain ⟨v, hv, hzv⟩ := M.cocycle_eq_coneSingle hz K₀ hK₀
    rw [hΨ, hzv]
    by_cases hcd : c = d
    · subst hcd
      rw [coeffAt_coneSingle_same]
      exact ⟨hv, fun h => absurd hc (not_le.mpr h)⟩
    · rw [coeffAt_coneSingle_ne hcd]
      exact ⟨zero_mem _, fun _ => rfl⟩
  have hgood : ∀ z ∈ t, ∀ d, coeffAt S x d (Ψ z) ∈ (M.tildeSys d).secs ∧
      (d < c₁ → coeffAt S x d (Ψ z) = 0) := fun z hz => hG (ht z hz)

  let D : Finset ℤ := (t.biUnion fun z => coneSupp (Ψ z)).filter (c₁ ≤ ·)
  let e := (t ×ˢ D).equivFin.symm
  refine ⟨(t ×ˢ D).card, fun j => (e j).1.2, fun j => coeffAt S x (e j).1.2 (Ψ (e j).1.1),
    fun j => ?_, fun c hc y hy => ?_⟩
  · have hm := Finset.mem_product.mp (e j).2
    exact ⟨(Finset.mem_filter.mp hm.2).2, (hgood _ hm.1 _).1⟩
  obtain ⟨z, hz, hzy⟩ := M.exists_cocycle_of_mem_secs hy
  have hzt : z ∈ H0tail M.coneGraded c₁ :=
    (le_iSup₂ (f := fun c (_ : c₁ ≤ c) =>
      Cech.cocyDeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS 0) c hc) hz
  let Sp : ℤ → Submodule S Ω := fun d => Submodule.span S {w | ∃ (j : Fin (t ×ˢ D).card) (f : Poly S N)
    (k : ℕ), f.IsHomogeneous k ∧ (k : ℤ) + (e j).1.2 = d ∧ w = aeval x f * coeffAt S x (e j).1.2 (Ψ (e j).1.1)}
  have hmulSp : ∀ (f : Poly S N) (k : ℕ), f.IsHomogeneous k → ∀ d, ∀ u ∈ Sp (d - k),
      aeval x f * u ∈ Sp d := by
    intro f k hf d u hu
    refine Submodule.span_induction (p := fun u _ => aeval x f * u ∈ Sp d) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨j, g, k', hg, hgk, rfl⟩
      exact Submodule.subset_span ⟨j, f * g, k + k', hf.mul hg, by push_cast; omega,
        by rw [map_mul, mul_assoc]⟩
    · rw [mul_zero]; exact zero_mem _
    · intro a b _ _ ha hb; rw [mul_add]; exact add_mem ha hb
    · intro s a _ ha; rw [mul_smul_comm]; exact Submodule.smul_mem _ s ha
  have key : ∀ w ∈ Submodule.span (Poly S N) (t : Set (Cech.Cochain (locSys S N M.coneSub) 0)),
      ∀ d, coeffAt S x d (Ψ w) ∈ Sp d := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => ∀ d, coeffAt S x d (Ψ w) ∈ Sp d) ?_ ?_ ?_ ?_ hw
    · intro z' hz' d
      by_cases h0 : coeffAt S x d (Ψ z') = 0
      · rw [h0]; exact zero_mem _
      · have hd : c₁ ≤ d := by
          by_contra hlt
          exact h0 ((hgood z' hz' d).2 (not_le.mp hlt))
        have hmem : (z', d) ∈ t ×ˢ D := Finset.mem_product.mpr ⟨hz', Finset.mem_filter.mpr
          ⟨Finset.mem_biUnion.mpr ⟨z', hz', mem_coneSupp.mpr h0⟩, hd⟩⟩
        refine Submodule.subset_span ⟨e.symm ⟨(z', d), hmem⟩, 1, 0, isHomogeneous_one _ _, ?_, ?_⟩
        · simp
        · simp
    · intro d; rw [map_zero, map_zero]; exact zero_mem _
    · intro a b _ _ ha hb d; rw [map_add, map_add]; exact add_mem (ha d) (hb d)
    · intro p a _ ha d
      rw [map_smul, ← sum_homogeneousComponent p, Finset.sum_smul, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [coeffAt_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous k p)]
      exact hmulSp _ k (homogeneousComponent_isHomogeneous k p) d _ (ha (d - k))
  have hyc := key z (hspan hzt) c
  rwa [hΨ, hzy K₀ hK₀, coeffAt_coneSingle_same] at hyc
end TildeTail
end GroundTheory.Heights₂.Heights.Kleiman
