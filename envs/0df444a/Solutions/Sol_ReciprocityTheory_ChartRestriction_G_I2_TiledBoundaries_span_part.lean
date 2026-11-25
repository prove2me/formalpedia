-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.span_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:32:44.738213+00:00
-- url     : https://prove2.me/submissions/a41bf50e-d0fe-4af8-8101-578ee6525c27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_l2Inner_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_l2Inner_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_l2Inner_zero_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
private theorem continuous_of_mem_Sec (X : PT E) {q n : ℕ} {F : (Fin n → Vsp X.dim) → ℂ}
    (hF : F ∈ X.Sec q n) : Continuous F :=
  hF.1.continuous
end
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (hI : StepI) (hPos : StepPos) (hKc : StepK) (hD : StepD) (X : PT E) {q n : ℕ}
    {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) (hs0 : s ≠ 0) {K : Finset (Fin n → Vsp X.dim)} (hK : IsReps X q n π K)
    (h1 : ∀ b ∈ K, X.U q b (s0 X π s) ∈ X.Sec q n)
    (h2 : ∀ b ∈ K, ∀ b' ∈ K, b ≠ b' → X.l2ip q (X.U q b (s0 X π s)) (X.U q b' (s0 X π s)) = 0)
    (h3 : ∀ b ∈ K, X.l2 q (X.U q b (s0 X π s)) = X.l2 1 s ^ n) :
    X.Sec q n ≤ Submodule.span ℂ ((fun b => X.U q b (s0 X π s)) '' (K : Set _)) := by
  obtain ⟨f, hf⟩ : ∃ f : ↥K → (Fin n → Vsp X.dim) → ℂ, ∀ i, f i = X.U q i.1 (s0 X π s) :=
    ⟨fun i => X.U q i.1 (s0 X π s), fun _ => rfl⟩
  have hcont : ∀ i, Continuous (f i) := fun i => by
    rw [hf]; exact continuous_of_mem_Sec X (h1 i.1 i.2)
  have hpos : 0 < X.l2 1 s := hPos E X 1 1 s hs hs0

  have hli : LinearIndependent ℂ f := by
    rw [linearIndependent_iff']
    intro t g hg i hi
    have hfun : (fun v => ∑ j ∈ t, g j * f j v) = 0 := by
      rw [← hg]; funext v; simp [Finset.sum_apply]
    have e := l2Inner_sum_left hI X q t g f (f i) hcont (hcont i)
    rw [hfun, l2Inner_zero_left, Finset.sum_eq_single i] at e
    · rw [l2Inner_self, hf i, h3 i.1 i.2] at e
      exact (mul_eq_zero.1 e.symm).resolve_right (Complex.ofReal_ne_zero.2 (pow_pos hpos n).ne')
    · intro j _ hji
      rw [hf j, hf i, h2 j.1 j.2 i.1 i.2 (fun h => hji (Subtype.ext h)), mul_zero]
    · intro h; exact absurd hi h
  have hrange : Set.range f = (fun b => X.U q b (s0 X π s)) '' (K : Set _) := by
    ext x; simp [hf]
  haveI : FiniteDimensional ℂ (X.Sec q n) := (hD E X q n hq).1
  have hle : Submodule.span ℂ (Set.range f) ≤ X.Sec q n := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [hf]; exact h1 i.1 i.2

  have heq := Submodule.eq_of_le_of_finrank_le hle (by
    rw [finrank_span_eq_card hli, Fintype.card_coe]
    exact (hD E X q n hq).2.trans (hKc E X q n π hq hπ K hK))
  rw [← hrange]
  exact heq.ge
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
