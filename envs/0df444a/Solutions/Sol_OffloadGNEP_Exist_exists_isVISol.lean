-- Prove2me | solution 1 for OffloadGNEP.Exist.exists_isVISol
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:50:44.181015+00:00
-- url     : https://prove2.me/submissions/12b0c004-9766-4993-8182-fdb9d5b0d38b

import Mathlib
import Definitions.Def_OffloadGNEP_Exist_Setting
import Theorems.Thm_OffloadGNEP_Exist_F_continuousOn_K_and_K_isCompact
import Theorems.Thm_ChanPangGQVI_ProjExistence_theorem_5_2

open OffloadGNEP.Exist

theorem solution {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (hne : ∀ u, (Ktil P u).Nonempty) : ∃ xb, IsVISol (K P) (F P) xb := by
  obtain ⟨hFc, hKc, hKcv⟩ := F_continuousOn_K_and_K_isCompact P hA hS
  -- K is nonempty: move each user's cloudlet share to the cloud
  have hKne : (K P).Nonempty := by
    choose y hy using hne
    let x0 : Fin N → Tier → ℝ := fun u i =>
      match i with
      | .m => y u .m
      | .clet => 0
      | .cloud => y u .clet + y u .cloud
    refine ⟨x0, fun u => ?_, ?_⟩
    · obtain ⟨h0, h1, h2, h3⟩ := hy u
      refine ⟨fun i => ?_, ?_, ?_, ?_⟩
      · cases i
        · exact h0 .m
        · exact le_refl _
        · exact add_nonneg (h0 .clet) (h0 .cloud)
      · show y u .m + 0 + (y u .clet + y u .cloud) = 1; linarith
      · show 0 + (y u .clet + y u .cloud) ≤ P.chi; linarith
      · show P.alpha u * P.Pm u * y u .m + P.beta u * P.Pt u * (0 + (y u .clet + y u .cloud)) ≤ _
        simpa using h3
    · show load P x0 ≤ P.Umax
      have : load P x0 = 0 := by simp [load, x0]
      rw [this]; exact hA.1.le
  -- transport to Euclidean space
  let ι := Fin N × Tier
  let σ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let g : (Fin N → Tier → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (Fintype.card ι)) :=
    { toFun := fun x => WithLp.toLp 2 (fun k => x (σ.symm k).1 (σ.symm k).2)
      map_add' := by intro x y; ext k; simp
      map_smul' := by intro a x; ext k; simp }
  let ginv : EuclideanSpace ℝ (Fin (Fintype.card ι)) → (Fin N → Tier → ℝ) :=
    fun z u i => z (σ (u, i))
  have hg_apply : ∀ x k, g x k = x (σ.symm k).1 (σ.symm k).2 := fun x k => rfl
  have hginv_g : ∀ x, ginv (g x) = x := by
    intro x; funext u i; simp [ginv, hg_apply]
  have hg_cont : Continuous g := LinearMap.continuous_of_finiteDimensional g
  have hginv_cont : Continuous ginv := by
    apply continuous_pi; intro u; apply continuous_pi; intro i
    exact (PiLp.continuous_apply 2 _ (σ (u, i)))
  have hinner : ∀ a b, inner ℝ (g a) (g b) = pair a b := by
    intro a b
    rw [PiLp.inner_apply]
    simp only [hg_apply, RCLike.inner_apply, conj_trivial]
    rw [pair, ← Fintype.sum_prod_type']
    rw [← Equiv.sum_comp σ.symm]
    apply Fintype.sum_congr; intro k; ring
  let C := g '' K P
  have hC := ChanPangGQVI.ProjExistence.theorem_5_2 (fun _ => C) (fun z => g (F P (ginv z))) C
    (hKne.image _) (hKc.image hg_cont) (hKcv.linear_image g) (fun _ _ => le_refl _)
    (by
      apply hg_cont.comp_continuousOn
      apply hFc.comp hginv_cont.continuousOn
      rintro _ ⟨x, hx, rfl⟩
      simpa [hginv_g] using hx)
    (fun _ _ => hKne.image _) SemicontinuousOn.const SemicontinuousOn.const
    (fun _ _ => hKcv.linear_image g) (fun _ _ => (hKc.image hg_cont).isClosed)
  obtain ⟨z, w, hz, hw, hzw⟩ := hC
  obtain ⟨xb, hxb, rfl⟩ := hz
  simp only [Set.mem_singleton_iff] at hw
  subst hw
  refine ⟨xb, hxb, fun x hx => ?_⟩
  have := hzw (g x) ⟨x, hx, rfl⟩
  rw [hginv_g, ← map_sub, hinner] at this
  rw [pair] at this ⊢
  simpa [mul_comm] using this
