-- Prove2me | solution 1 for TensorRankN2M.ThreeTwoM.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:39:29.866355+00:00
-- url     : https://prove2.me/submissions/078eaa07-de74-4f82-8055-2183d0f6c787

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_Decomposition
import Definitions.Def_TensorRankN2M_ThreeTwoM_Normalization

section
set_option autoImplicit false

namespace TensorRankN2M.Dev.Common

open TensorRankN2M.ThreeTwoM

variable {𝔽 : Type*} [Field 𝔽] {k l m R : ℕ}

theorem W_D_Bvec (d : Decomposition 𝔽 k l m R) (A : Matrix (Fin k) (Fin l) 𝔽)
    (B : Matrix (Fin l) (Fin m) 𝔽) : d.W ((d.D A).mulVec (d.Bvec B)) = A * B := by
  rw [d.eq A B]
  simp [Decomposition.W, Decomposition.D, Decomposition.Bvec, Fintype.linearCombination_apply,
    Matrix.mulVec_diagonal]

theorem Bvec_injective [NeZero k] (d : Decomposition 𝔽 k l m R) :
    Function.Injective d.Bvec := by
  rw [injective_iff_map_eq_zero]
  intro B hB
  have h0 : ∀ A : Matrix (Fin k) (Fin l) 𝔽, A * B = 0 := by
    intro A
    rw [← W_D_Bvec d A B, hB]
    simp
  ext i j
  have h1 := congrFun (congrFun (h0 (Matrix.single (0 : Fin k) i (1 : 𝔽))) 0) j
  simpa [Matrix.mul_apply, Matrix.single_apply] using h1

end TensorRankN2M.Dev.Common
end

section
set_option autoImplicit false

namespace TensorRankN2M.Dev.Lemma8

open TensorRankN2M.ThreeTwoM

variable {𝔽 : Type*} [Field 𝔽] {k l m R : ℕ}

theorem f_apply [NeZero l] (d : Decomposition 𝔽 k l m R) (i : Fin k)
    (v : Matrix (Fin l) (Fin m) 𝔽) (r : Fin R) :
    d.f i v r = d.α r (Matrix.single i 0 1) * d.β r v := by
  simp [Decomposition.f, Decomposition.D, Decomposition.Bvec, Matrix.mulVec_diagonal]

theorem unit_alpha [NeZero k] [NeZero l] (d : Decomposition 𝔽 k l m R)
    (hd : d.StronglyNormalized) (r : Fin R) : d.α r (Matrix.single 0 0 1) ≠ 0 := by
  have h := hd.2
  unfold Decomposition.D at h
  rw [Matrix.isUnit_diagonal] at h
  exact (Pi.isUnit_iff.mp h r).ne_zero

/-- the flag -/
def E (𝔽 : Type*) [Field 𝔽] (R j : ℕ) : Submodule 𝔽 (Fin R → 𝔽) where
  carrier := {x | ∀ r : Fin R, j ≤ r.val → x r = 0}
  add_mem' := by intro a b ha hb r hr; simp [ha r hr, hb r hr]
  zero_mem' := by intro r _; rfl
  smul_mem' := by intro c a ha r hr; simp [ha r hr]

theorem f_mem_E [NeZero k] [NeZero l] (d : Decomposition 𝔽 k l m R)
    (hd : d.StronglyNormalized) (j : ℕ) (i : Fin k) (v : Matrix (Fin l) (Fin m) 𝔽)
    (hv : d.f 0 v ∈ E 𝔽 R j) : d.f i v ∈ E 𝔽 R j := by
  intro r hr
  have h := hv r hr
  rw [f_apply] at h ⊢
  have h1 : d.β r v = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (unit_alpha d hd r)
    · exact h
  rw [h1, mul_zero]

theorem f0_injective [NeZero k] [NeZero l] (d : Decomposition 𝔽 k l m R)
    (hd : d.StronglyNormalized) : Function.Injective (d.f 0) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  apply Common.Bvec_injective d
  ext r
  have h := congrFun hv r
  rw [f_apply] at h
  simp only [Pi.zero_apply] at h ⊢
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (unit_alpha d hd r)
  · simpa [Decomposition.Bvec] using h

end TensorRankN2M.Dev.Lemma8

namespace TensorRankN2M.ThreeTwoM

open TensorRankN2M.Dev.Lemma8

theorem chk_lemma_8 {𝔽 : Type*} [Field 𝔽] [IsAlgClosed 𝔽] {k l m R : ℕ} [NeZero k] [NeZero l]
    (d : Decomposition 𝔽 k l m R) (hd : d.StronglyNormalized)
    (S : Submodule 𝔽 (Matrix (Fin l) (Fin m) 𝔽)) (hS : S ≠ ⊥) :
    Module.finrank 𝔽 S + (k - 1) ≤ Module.finrank 𝔽 ↥(⨆ i : Fin k, S.map (d.f i)) := by
  classical
  set F0 : Submodule 𝔽 (Fin R → 𝔽) := S.map (d.f 0) with hF0
  have hR : F0 ⊓ E 𝔽 R R ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    rw [Submodule.ne_bot_iff]
    refine ⟨d.f 0 v, ⟨Submodule.mem_map_of_mem hv, ?_⟩, ?_⟩
    · intro r hr; exact absurd r.2 (by omega)
    · exact fun h => hv0 (f0_injective d hd (by simpa using h))
  have hex : ∃ j, F0 ⊓ E 𝔽 R j ≠ ⊥ := ⟨R, hR⟩
  set j := Nat.find hex with hj
  have hjne : F0 ⊓ E 𝔽 R j ≠ ⊥ := Nat.find_spec hex
  have hjR : j ≤ R := Nat.find_min' hex hR
  have hj0 : j ≠ 0 := by
    intro h0
    apply hjne
    rw [Submodule.eq_bot_iff]
    rintro x ⟨-, hx⟩
    funext r
    exact hx r (by omega)
  have hjlt : F0 ⊓ E 𝔽 R (j - 1) = ⊥ := by
    by_contra h
    exact Nat.find_min hex (by omega : j - 1 < j) h
  have hU : Module.finrank 𝔽 ↥(F0 ⊓ E 𝔽 R j) ≤ 1 := by
    let idx : Fin R := ⟨j - 1, by omega⟩
    let φ : ↥(F0 ⊓ E 𝔽 R j) →ₗ[𝔽] 𝔽 := (LinearMap.proj idx).comp (F0 ⊓ E 𝔽 R j).subtype
    have hφ : Function.Injective φ := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have hx0 : (x : Fin R → 𝔽) idx = 0 := hx
      have hmem : (x : Fin R → 𝔽) ∈ F0 ⊓ E 𝔽 R (j - 1) := by
        refine ⟨x.2.1, ?_⟩
        intro r hr
        by_cases h : r.val = j - 1
        · have : r = idx := Fin.ext h
          rw [this]; exact hx0
        · exact x.2.2 r (by omega)
      rw [hjlt] at hmem
      exact Subtype.ext (by simpa using hmem)
    simpa using LinearMap.finrank_le_finrank_of_injective hφ
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hjne
  obtain ⟨v, hvS, hvx⟩ := hx.1
  have hfv : d.f 0 v ∈ E 𝔽 R j := by rw [hvx]; exact hx.2
  have hv0 : v ≠ 0 := by rintro rfl; exact hx0 (by simp at hvx; exact hvx.symm)
  set T : Submodule 𝔽 (Fin R → 𝔽) := Submodule.span 𝔽 (Set.range fun i : Fin k => d.f i v) with hT
  have hTdim : Module.finrank 𝔽 T = k := by
    rw [hT, finrank_span_eq_card (hd.1 v hv0)]; simp
  have hTE : T ≤ E 𝔽 R j := by
    rw [hT, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact f_mem_E d hd j i v hfv
  have hinf : Module.finrank 𝔽 ↥(F0 ⊓ T) ≤ 1 := by
    refine le_trans (Submodule.finrank_mono ?_) hU
    exact inf_le_inf_left _ hTE
  have hF0dim : Module.finrank 𝔽 F0 = Module.finrank 𝔽 S :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (f0_injective d hd) S)).symm
  have hsub : F0 ⊔ T ≤ ⨆ i : Fin k, S.map (d.f i) := by
    refine sup_le (le_iSup (fun i : Fin k => S.map (d.f i)) 0) ?_
    rw [hT, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (le_iSup (fun i : Fin k => S.map (d.f i)) i) (Submodule.mem_map_of_mem hvS)
  have h1 := Submodule.finrank_mono hsub
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq F0 T
  rw [hF0dim, hTdim] at h2
  have hk : 1 ≤ k := NeZero.one_le
  omega

end TensorRankN2M.ThreeTwoM
end

theorem solution : type_of% @TensorRankN2M.ThreeTwoM.chk_lemma_8 := @TensorRankN2M.ThreeTwoM.chk_lemma_8
