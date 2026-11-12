-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P28.marginalExtremum
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T00:48:12.488997+00:00
-- url     : https://prove2.me/submissions/7643e320-a461-4154-be7b-a2958f116ed2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P28

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Aux_marginalExtremum

theorem cvx {E F : Type} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (S : Set E) (T : Set F) (hS : Convex ℝ S) (hT : Convex ℝ T) (hne : T.Nonempty)
    (f : E × F → ℝ) (hf : ConvexOn ℝ (S ×ˢ T) f)
    (hb : ∀ x ∈ S, BddBelow (Set.range fun y : T => f (x,y))) :
    ConvexOn ℝ S (fun x => sInf (Set.range fun y : T => f (x,y))) := by
  refine ⟨hS, ?_⟩
  intro x1 hx1 x2 hx2 a b ha hb' hab
  have hz : a • x1 + b • x2 ∈ S := hS hx1 hx2 ha hb' hab
  haveI : Nonempty T := hne.to_subtype
  obtain ⟨I1, hI1⟩ : ∃ I, I = sInf (Set.range fun y : T => f (x1,y)) := ⟨_, rfl⟩
  obtain ⟨I2, hI2⟩ : ∃ I, I = sInf (Set.range fun y : T => f (x2,y)) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = sInf (Set.range fun y : T => f (a • x1 + b • x2,y)) := ⟨_, rfl⟩
  show sInf (Set.range fun y : T => f (a • x1 + b • x2,y)) ≤
    a * sInf (Set.range fun y : T => f (x1,y)) + b * sInf (Set.range fun y : T => f (x2,y))
  rw [← hI1, ← hI2, ← hL]
  apply le_of_forall_pos_le_add
  intro ε hε
  have k1 : sInf (Set.range fun y : T => f (x1,y)) < I1 + ε := by rw [← hI1]; linarith
  have k2 : sInf (Set.range fun y : T => f (x2,y)) < I2 + ε := by rw [← hI2]; linarith
  obtain ⟨_, ⟨y1, rfl⟩, hy1⟩ := exists_lt_of_csInf_lt (Set.range_nonempty _) k1
  obtain ⟨_, ⟨y2, rfl⟩, hy2⟩ := exists_lt_of_csInf_lt (Set.range_nonempty _) k2
  have e1 : f (x1, (y1 : F)) < I1 + ε := hy1
  have e2 : f (x2, (y2 : F)) < I2 + ε := hy2
  have hy : a • (y1:F) + b • (y2:F) ∈ T := hT y1.2 y2.2 ha hb' hab
  have h1 : L ≤ f (a • x1 + b • x2, a • (y1:F) + b • (y2:F)) := by
    rw [hL]; exact csInf_le (hb _ hz) ⟨⟨_, hy⟩, rfl⟩
  have h2 : f (a • x1 + b • x2, a • (y1:F) + b • (y2:F)) ≤ a * f (x1, y1) + b * f (x2, y2) := by
    have := hf.2 (Set.mk_mem_prod hx1 y1.2) (Set.mk_mem_prod hx2 y2.2) ha hb' hab
    first
      | exact this
      | simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using this
  have m1 := mul_le_mul_of_nonneg_left e1.le ha
  have m2 := mul_le_mul_of_nonneg_left e2.le hb'
  have hε' : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
  nlinarith

theorem ccv {E F : Type} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (S : Set E) (T : Set F) (hS : Convex ℝ S) (hT : Convex ℝ T) (hne : T.Nonempty)
    (f : E × F → ℝ) (hf : ConcaveOn ℝ (S ×ˢ T) f)
    (hb : ∀ x ∈ S, BddAbove (Set.range fun y : T => f (x,y))) :
    ConcaveOn ℝ S (fun x => sSup (Set.range fun y : T => f (x,y))) := by
  refine ⟨hS, ?_⟩
  intro x1 hx1 x2 hx2 a b ha hb' hab
  have hz : a • x1 + b • x2 ∈ S := hS hx1 hx2 ha hb' hab
  haveI : Nonempty T := hne.to_subtype
  obtain ⟨I1, hI1⟩ : ∃ I, I = sSup (Set.range fun y : T => f (x1,y)) := ⟨_, rfl⟩
  obtain ⟨I2, hI2⟩ : ∃ I, I = sSup (Set.range fun y : T => f (x2,y)) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = sSup (Set.range fun y : T => f (a • x1 + b • x2,y)) := ⟨_, rfl⟩
  show a * sSup (Set.range fun y : T => f (x1,y)) + b * sSup (Set.range fun y : T => f (x2,y)) ≤
    sSup (Set.range fun y : T => f (a • x1 + b • x2,y))
  rw [← hI1, ← hI2, ← hL]
  apply le_of_forall_pos_le_add
  intro ε hε
  have k1 : I1 - ε < sSup (Set.range fun y : T => f (x1,y)) := by rw [← hI1]; linarith
  have k2 : I2 - ε < sSup (Set.range fun y : T => f (x2,y)) := by rw [← hI2]; linarith
  obtain ⟨_, ⟨y1, rfl⟩, hy1⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) k1
  obtain ⟨_, ⟨y2, rfl⟩, hy2⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) k2
  have e1 : I1 - ε < f (x1, (y1 : F)) := hy1
  have e2 : I2 - ε < f (x2, (y2 : F)) := hy2
  have hy : a • (y1:F) + b • (y2:F) ∈ T := hT y1.2 y2.2 ha hb' hab
  have h1 : f (a • x1 + b • x2, a • (y1:F) + b • (y2:F)) ≤ L := by
    rw [hL]; exact le_csSup (hb _ hz) ⟨⟨_, hy⟩, rfl⟩
  have h2 : a * f (x1, y1) + b * f (x2, y2) ≤ f (a • x1 + b • x2, a • (y1:F) + b • (y2:F)) := by
    have := hf.2 (Set.mk_mem_prod hx1 y1.2) (Set.mk_mem_prod hx2 y2.2) ha hb' hab
    first
      | exact this
      | simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using this
  have m1 := mul_le_mul_of_nonneg_left e1.le ha
  have m2 := mul_le_mul_of_nonneg_left e2.le hb'
  have hε' : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
  nlinarith

end Aux_marginalExtremum

theorem solution
    {E F : Type} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (S : Set E) (T : Set F) (hS : Convex ℝ S) (hT : Convex ℝ T) (hne : T.Nonempty)
    (f : E × F → ℝ) :
    ((ConvexOn ℝ (S ×ˢ T) f ∧
      ∀ x ∈ S, BddBelow (Set.range fun y : T => f (x,y))) →
      ConvexOn ℝ S (fun x => sInf (Set.range fun y : T => f (x,y)))) ∧
    ((ConcaveOn ℝ (S ×ˢ T) f ∧
      ∀ x ∈ S, BddAbove (Set.range fun y : T => f (x,y))) →
      ConcaveOn ℝ S (fun x => sSup (Set.range fun y : T => f (x,y)))) :=
  ⟨fun h => Aux_marginalExtremum.cvx S T hS hT hne f h.1 h.2,
   fun h => Aux_marginalExtremum.ccv S T hS hT hne f h.1 h.2⟩

end
