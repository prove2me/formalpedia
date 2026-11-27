-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_YYRatioBasis_proof_629de21163cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:02:16.104492+00:00
-- url     : https://prove2.me/submissions/6b3bdd8c-149d-40e0-9063-361b65eb361f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StYYRatioBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StMobiusAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PYYRatioBasis
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isAlgebraic_map_of_map_le_795ccb6161b2

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.T
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace YYRatioBasis
theorem _root_.solution (hM : MobiusAlgIndep.Statement) : YYRatioBasis.Statement := by
  intro Ω _ _ ι ν κ _ _ _ E _ _ Φ _ _ _ x e b φ δ g i₀ l₀ k₀ k₁ d t a hx ht htF htalg hδ hδF hφb hgF hD ha
  let f : Ω →ₐ[ℚ] Φ := IsScalarTower.toAlgHom ℚ Ω Φ
  have hf : ∀ z, f z = algebraMap Ω Φ z := fun _ => rfl
  have hφe : ∀ k p, φ k (e p) = x i₀ * (b.repr (e p) 0 * g k 0 + b.repr (e p) 1 * g k 1) := by
    intro k p
    conv_lhs => rw [← b.sum_repr (e p)]
    simp only [map_add, map_smul, Fin.sum_univ_two, hφb, smul_eq_mul]; ring
  have hB : b.repr (e 0) 0 * b.repr (e 1) 1 - b.repr (e 1) 0 * b.repr (e 0) 1 ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det (b.toMatrix_mul_toMatrix_flip e)
    rw [Matrix.det_mul, Matrix.det_one, Matrix.det_fin_two] at h
    simp only [Module.Basis.toMatrix_apply, h0, zero_mul] at h
    exact zero_ne_one h
  have hdet : φ k₁ (e 0) * φ k₀ (e 1) - φ k₁ (e 1) * φ k₀ (e 0) ≠ 0 := by
    have : φ k₁ (e 0) * φ k₀ (e 1) - φ k₁ (e 1) * φ k₀ (e 0) = -(x i₀ ^ 2 *
        (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0) * (b.repr (e 0) 0 * b.repr (e 1) 1 - b.repr (e 1) 0 * b.repr (e 0) 1)) := by
      rw [hφe, hφe, hφe, hφe]; ring
    rw [this]; exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hx) hD) hB)
  obtain ⟨hden, hmob⟩ := hM Ω Φ 1 (fun _ => a) (φ k₁ (e 0)) (φ k₁ (e 1)) (φ k₀ (e 0)) (φ k₀ (e 1))
    (algebraicIndependent_unique_type_iff.mpr ha) hdet
  have hu : lineVal e (φ k₀) a ≠ 0 := hden 0
  set r := lineVal e (φ k₁) a / lineVal e (φ k₀) a with hr
  have hy : AlgebraicIndependent Ω (fun _ : Fin 1 => r) := hmob
  let σ : Fin (d + 1) ≃ Fin 1 ⊕ Fin d := finSumFinEquiv.symm.trans (Equiv.sumComm _ _)
  let t' : Fin (d + 1) → Φ := Sum.elim (fun _ : Fin 1 => r) (algebraMap Ω Φ ∘ t) ∘ σ
  have ht' : ∀ n, t' n = r ∨ ∃ m, t' n = f (t m) := by
    intro n; rcases h : σ n with j | m
    · exact Or.inl (by simp [t', h])
    · exact Or.inr ⟨m, by simp [t', h, hf]⟩
  have hr_mem : r ∈ Set.range t' := ⟨σ.symm (Sum.inl 0), by simp [t']⟩
  have ht_mem : ∀ m, f (t m) ∈ Set.range t' := fun m => ⟨σ.symm (Sum.inr m), by simp [t', hf]⟩
  let c : ∀ k, T.yyIdx ι ν κ k := fun | .base => i₀ | .det => l₀ | .line => k₀
  set S := coneRatios (T.yyCoord x δ e φ a) c
  set F := IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)
  have hF : ∀ z ∈ F, f z ∈ F.map f := fun z hz => ⟨z, hz, rfl⟩
  refine ⟨c, t', ?_, (AlgebraicIndependent.sumElim_comp ht hy).comp σ σ.injective, ?_, ?_⟩
  · rintro (_ | _ | _)
    · exact (map_ne_zero _).mpr hx
    · exact (map_ne_zero _).mpr hδ
    · exact hu
  · have hFS : F.map f ≤ IntermediateField.adjoin ℚ S := by
      rw [IntermediateField.adjoin_map]
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      refine IntermediateField.subset_adjoin _ _ ⟨⟨.base, j⟩, ?_⟩
      show algebraMap Ω Φ (x j) / algebraMap Ω Φ (x i₀) = f (x j / x i₀)
      rw [hf, map_div₀]
    intro n
    rcases ht' n with h | ⟨m, h⟩ <;> rw [h]
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨.line, k₁⟩, rfl⟩
    · exact hFS (hF _ (htF m))
  · set M := IntermediateField.adjoin ℚ (Set.range t')
    let A := (algebraicClosure M Φ).restrictScalars ℚ
    have hMA : ∀ z ∈ M, z ∈ A := fun z hz =>
      mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (⟨z, hz⟩ : M))
    have hLM : (IntermediateField.adjoin ℚ (Set.range t)).map f ≤ M := by
      rw [IntermediateField.adjoin_map]
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      exact IntermediateField.subset_adjoin _ _ (ht_mem m)
    have hFA : F.map f ≤ A := by
      rw [IntermediateField.adjoin_map]
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      exact mem_algebraicClosure_iff.mpr (isAlgebraic_map_of_map_le f hLM (htalg j))
    have hFA' : ∀ z ∈ F, f z ∈ A := fun z hz => hFA (hF z hz)
    have hrA : r ∈ A := hMA r (IntermediateField.subset_adjoin _ _ hr_mem)
    have key : ∀ k, lineVal e (φ k) a = f (x i₀) * (f (g k 0) * (f (b.repr (e 0) 0) + a * f (b.repr (e 1) 0)) +
        f (g k 1) * (f (b.repr (e 0) 1) + a * f (b.repr (e 1) 1))) := by
      intro k; simp only [lineVal, hφe, map_add, map_mul, hf]; ring
    have hD' : f (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0) ≠ 0 := (map_ne_zero f).mpr hD
    have hline : ∀ k, lineVal e (φ k) a / lineVal e (φ k₀) a = (f (g k 0) * (f (g k₁ 1) - f (g k₀ 1) * r) +
        f (g k 1) * (f (g k₀ 0) * r - f (g k₁ 0))) / f (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0) := by
      intro k
      have hkey : f (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0) * lineVal e (φ k) a =
          f (g k 0) * (f (g k₁ 1) * lineVal e (φ k₀) a - f (g k₀ 1) * lineVal e (φ k₁) a) +
          f (g k 1) * (f (g k₀ 0) * lineVal e (φ k₁) a - f (g k₁ 0) * lineVal e (φ k₀) a) := by
        rw [key k, key k₀, key k₁, map_sub, map_mul, map_mul]; ring
      rw [hr, eq_div_iff hD']
      field_simp
      linear_combination hkey
    intro s hs
    suffices s ∈ A from mem_algebraicClosure_iff.mp this
    obtain ⟨⟨k, i⟩, rfl⟩ := hs
    cases k
    · show algebraMap Ω Φ (x i) / algebraMap Ω Φ (x i₀) ∈ A
      rw [← map_div₀]
      exact hFA' _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    · show algebraMap Ω Φ (δ i) / algebraMap Ω Φ (δ l₀) ∈ A
      rw [← map_div₀]
      exact hFA' _ (hδF i)
    · show lineVal e (φ i) a / lineVal e (φ k₀) a ∈ A
      rw [hline i]
      have hg : ∀ k q, f (g k q) ∈ A := fun k q => hFA' _ (hgF k q)
      refine div_mem (add_mem (mul_mem (hg _ _) (sub_mem (hg _ _) (mul_mem (hg _ _) hrA)))
        (mul_mem (hg _ _) (sub_mem (mul_mem (hg _ _) hrA) (hg _ _)))) ?_
      exact hFA' _ (sub_mem (mul_mem (hgF _ _) (hgF _ _)) (mul_mem (hgF _ _) (hgF _ _)))
end YYRatioBasis
end GroundTheory.Heights₂.Heights.Inter
