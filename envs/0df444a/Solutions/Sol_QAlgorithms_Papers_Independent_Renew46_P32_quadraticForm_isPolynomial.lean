-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P32.quadraticForm_isPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:17:04.73359+00:00
-- url     : https://prove2.me/submissions/09d81d1c-e14d-48d0-bbc0-d2e3d7e926fe

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

open QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

section G66B
variable {K : Type u} [CommRing K] {E : Type u} [AddCommGroup E] [Module K E]
  {F : Type u} [AddCommGroup F] [Module K F]

theorem g66b_m2_addL (m : MultilinearMap K (fun _ : Fin 2 => E) F) (a b c : E) :
    m ![a + b, c] = m ![a, c] + m ![b, c] := by
  have := m.map_update_add ![a, c] 0 a b
  convert this using 2 <;> (try congr 1) <;> (funext i; fin_cases i <;> simp)

theorem g66b_m2_addR (m : MultilinearMap K (fun _ : Fin 2 => E) F) (a b c : E) :
    m ![c, a + b] = m ![c, a] + m ![c, b] := by
  have := m.map_update_add ![c, a] 1 a b
  convert this using 2 <;> (try congr 1) <;> (funext i; fin_cases i <;> simp)

theorem g66b_m2_smulL (m : MultilinearMap K (fun _ : Fin 2 => E) F) (t : K) (a c : E) :
    m ![t • a, c] = t • m ![a, c] := by
  have := m.map_update_smul ![a, c] 0 t a
  convert this using 2 <;> (try congr 1) <;> (funext i; fin_cases i <;> simp)

theorem g66b_m2_smulR (m : MultilinearMap K (fun _ : Fin 2 => E) F) (t : K) (a c : E) :
    m ![c, t • a] = t • m ![c, a] := by
  have := m.map_update_smul ![c, a] 1 t a
  convert this using 2 <;> (try congr 1) <;> (funext i; fin_cases i <;> simp)

/-- bilinear map as a 2-multilinear map -/
def g66b_ofBilin {D : Type u} [AddCommGroup D] [Module K D] (B : LinearMap.BilinMap K D F) :
    MultilinearMap K (fun _ : Fin 2 => D) F where
  toFun v := B (v 0) (v 1)
  map_update_add' := by
    intro _ v i a b
    fin_cases i
    · simp
    · simp
  map_update_smul' := by
    intro _ v i c a
    fin_cases i
    · simp
    · simp
end G66B

section AlgebraicDefinitions

variable {K : Type u} [CommRing K]

variable {E : Type u} [AddCommGroup E] [Module K E]

variable {F : Type u} [AddCommGroup F] [Module K F]

theorem solution
    (q : E → F) (hq : IsHomogeneousForm (K := K) 2 q) :
    IsHomogeneousPolynomial (K := K) 2 q := by
  obtain ⟨hhom, m, hm⟩ := hq
  intro D _ _ _ phi _
  have hq0 : q 0 = 0 := by
    have := hhom 0 0
    simpa using this
  have hlin : ∀ a b : E, q (a + b) = q a + q b + m ![b, a] := by
    intro a b
    rw [hm]
    show q (a + b) = q a + q b + (q (0 + a + b) - q (0 + a) - (q (0 + b) - q 0))
    simp only [zero_add, hq0, sub_zero]
    abel
  let Bm : LinearMap.BilinMap K D F := LinearMap.mk₂ K (fun x y => m ![phi y, phi x])
    (fun x1 x2 y => by simp only [map_add]; exact g66b_m2_addR m _ _ _)
    (fun c x y => by simp only [map_smul]; exact g66b_m2_smulR m _ _ _)
    (fun x y1 y2 => by simp only [map_add]; exact g66b_m2_addL m _ _ _)
    (fun c x y => by simp only [map_smul]; exact g66b_m2_smulL m _ _ _)
  let Q : QuadraticMap K D F :=
    { toFun := fun x => q (phi x)
      toFun_smul := fun a x => by
        simp only [map_smul]; rw [hhom, pow_two]
      exists_companion' := ⟨Bm, fun x y => by
        simp only [map_add, Bm, LinearMap.mk₂_apply]; exact hlin _ _⟩ }
  obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective Q
  refine ⟨g66b_ofBilin B, fun x => ?_⟩
  have := congrArg (fun Q' : QuadraticMap K D F => Q' x) hB
  simp only [LinearMap.BilinMap.toQuadraticMap_apply] at this
  rw [← show Q x = q (phi x) from rfl, ← this]
  rfl

end AlgebraicDefinitions
