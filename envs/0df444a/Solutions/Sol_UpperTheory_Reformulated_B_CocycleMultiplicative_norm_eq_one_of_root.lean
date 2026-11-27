-- Prove2me | solution 1 for UpperTheory.Reformulated.B.CocycleMultiplicative.norm_eq_one_of_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:33:57.798195+00:00
-- url     : https://prove2.me/submissions/ec88886e-f312-4118-9478-d69095f1afed

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CocycleMultiplicative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped Matrix.Norms.L2Operator in
private theorem UpperTheory.Reformulated.B.CocycleMultiplicative.norm_of_mem_spectrum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (h : star A * A = 1) {z : ℂ} (hz : z ∈ spectrum ℂ A) : ‖z‖ = (1 : ℝ) := by
  have hu : A ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
    ⟨h, mul_eq_one_comm.mp h⟩
  rcases subsingleton_or_nontrivial (Matrix (Fin n) (Fin n) ℂ) with hs | hn
  · exact absurd hz (by simp [spectrum.of_subsingleton])
  · simpa using spectrum.subset_circle_of_unitary hu hz
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.CocycleMultiplicative
theorem _root_.solution :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {n : ℕ}
      (γ : ↥(UpperTheory.Reformulated.B.CocycleMultiplicative.UE E n)) (τ : E →+* ℂ),
      ∀ z ∈ (Polynomial.map τ (↑(↑γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly).roots, ‖z‖ = (1 : ℝ) := by
  intro E _ _ _ n γ τ z hz
  have hγ := γ.2
  obtain ⟨g, hg⟩ := γ
  simp only at hz
  have hg' : UpperTheory.Reformulated.B.CocycleMultiplicative.cT (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom
      (↑g : Matrix (Fin n) (Fin n) E) * 1 * (↑g : Matrix (Fin n) (Fin n) E) = 1 := hg
  rw [Matrix.mul_one] at hg'
  have hroot : ((↑g : Matrix (Fin n) (Fin n) E).map τ).charpoly.IsRoot z := by
    rw [Matrix.charpoly_map]
    exact (Polynomial.mem_roots'.mp hz).2
  have hstar : star ((↑g : Matrix (Fin n) (Fin n) E).map τ) =
      (UpperTheory.Reformulated.B.CocycleMultiplicative.cT (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom
        (↑g : Matrix (Fin n) (Fin n) E)).map τ := by
    ext i j
    simp [UpperTheory.Reformulated.B.CocycleMultiplicative.cT, Matrix.star_apply]
  have hU : star ((↑g : Matrix (Fin n) (Fin n) E).map τ) * (↑g : Matrix (Fin n) (Fin n) E).map τ = 1 := by
    rw [hstar, ← Matrix.map_mul, hg', Matrix.map_one _ (map_zero τ) (map_one τ)]
  exact UpperTheory.Reformulated.B.CocycleMultiplicative.norm_of_mem_spectrum _ hU (Matrix.mem_spectrum_of_isRoot_charpoly hroot)
end UpperTheory.Reformulated.B.CocycleMultiplicative
