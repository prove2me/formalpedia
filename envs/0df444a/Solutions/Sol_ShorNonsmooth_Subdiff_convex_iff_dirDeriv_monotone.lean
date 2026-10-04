-- Prove2me | solution 1 for ShorNonsmooth.Subdiff.convex_iff_dirDeriv_monotone
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T07:17:37.071269+00:00
-- url     : https://prove2.me/submissions/472e1a29-4890-4ac9-9c77-88d0f6628fbf

import Mathlib
import Definitions.Def_ShorNonsmooth_Subdiff_DirDeriv


namespace ShorNonsmooth.Subdiff
open Set Filter
open scoped Topology RealInnerProductSpace
noncomputable section

theorem shor_line_combo {n : ℕ} (x v : EuclideanSpace ℝ (Fin n))
    (a b u w : ℝ) (huw : u+w=1) :
    u • (x+a • v)+w • (x+b • v)=x+(u*a+w*b) • v := by
  rw [smul_add,smul_add,smul_smul,smul_smul]
  calc u • x+(u*a) • v+(w • x+(w*b) • v)
      = (u • x+w • x)+((u*a) • v+(w*b) • v) := by abel
    _ = x+(u*a+w*b) • v := by rw [← add_smul,← add_smul,huw,one_smul]

theorem shor_line_convex_domain {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ M f)
    (x v : EuclideanSpace ℝ (Fin n)) :
    ConvexOn ℝ ((fun t : ℝ => x+t • v) ⁻¹' M) (fun t : ℝ => f (x+t • v)) := by
  refine ⟨?_,?_⟩
  · intro a ha b hb u w hu hw huw
    change x+(u*a+w*b) • v ∈ M
    rw [← shor_line_combo x v a b u w huw]
    exact hf.1 ha hb hu hw huw
  · intro a ha b hb u w hu hw huw
    have h := hf.2 ha hb hu hw huw
    simpa only [shor_line_combo x v a b u w huw,smul_eq_mul] using h

theorem shor_hasDir_iff_right {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) (d : ℝ) :
    HasOneSidedDirDeriv f x v d ↔
      HasDerivWithinAt (fun t : ℝ => f (x+t • v)) d (Ioi 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi : (0:ℝ) ∉ Ioi 0)]
  rw [slope_fun_def_field]
  simp only [HasOneSidedDirDeriv,sub_zero,zero_smul,add_zero]

theorem shor_direction_exists {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ M f)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior M)
    (v : EuclideanSpace ℝ (Fin n)) : ∃ d,HasOneSidedDirDeriv f x v d := by
  let S := (fun t : ℝ => x+t • v) ⁻¹' M
  have hS : (0:ℝ) ∈ interior S := by
    rw [mem_interior_iff_mem_nhds]
    have hc : Continuous (fun t : ℝ => x+t • v) := by fun_prop
    have hm : M ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
    have h := hc.continuousAt (x:=0) (by simpa using hm)
    exact h
  have hc := shor_line_convex_domain M f hf x v
  exact ⟨_,(shor_hasDir_iff_right f x v _).mpr
    (hc.hasDerivWithinAt_rightDeriv_of_mem_interior hS)⟩


end
end ShorNonsmooth.Subdiff


namespace ShorNonsmooth.Subdiff
open Set
noncomputable section

theorem shor_real_convex_of_right_mono (F D : ℝ → ℝ) (hF : Continuous F)
    (hD : ∀ t,HasDerivWithinAt F (D t) (Ioi t) t) (hm : Monotone D) :
    ConvexOn ℝ univ F := by
  have hupper : ∀ x y : ℝ,x<y → slope F x y ≤ D y := by
    intro x y hxy
    let B : ℝ → ℝ := fun t => F x+D y*(t-x)
    have hB : ∀ t,HasDerivAt B (D y) t := by
      intro t
      dsimp [B]
      simpa using (((hasDerivAt_id t).sub_const x).const_mul (D y)).const_add (F x)
    have h := image_le_of_deriv_right_le_deriv_boundary
      hF.continuousOn (fun t _ => (hD t).Ici_of_Ioi)
      (by simp [B] : F x ≤ B x)
      (fun t _ => (hB t).continuousAt.continuousWithinAt)
      (fun t _ => (hB t).hasDerivWithinAt)
      (fun t ht => hm ht.2.le)
      (by exact ⟨hxy.le,le_rfl⟩ : y ∈ Icc x y)
    rw [slope_def_field]
    apply (div_le_iff₀ (sub_pos.mpr hxy)).mpr
    dsimp [B] at h
    linarith
  have hlower : ∀ x y : ℝ,x<y → D x ≤ slope F x y := by
    intro x y hxy
    let B : ℝ → ℝ := fun t => -F x-D x*(t-x)
    have hB : ∀ t,HasDerivAt B (-D x) t := by
      intro t
      dsimp [B]
      simpa only [mul_one,sub_eq_add_neg,Pi.neg_apply,id_eq] using
        ((((hasDerivAt_id t).sub_const x).const_mul (D x)).neg.const_add (-F x))
    have h := image_le_of_deriv_right_le_deriv_boundary
      hF.neg.continuousOn (fun t _ => (hD t).neg.Ici_of_Ioi)
      (by simp [B] : -F x ≤ B x)
      (fun t _ => (hB t).continuousAt.continuousWithinAt)
      (fun t _ => (hB t).hasDerivWithinAt)
      (fun t ht => neg_le_neg (hm ht.1))
      (by exact ⟨hxy.le,le_rfl⟩ : y ∈ Icc x y)
    rw [slope_def_field]
    apply (le_div_iff₀ (sub_pos.mpr hxy)).mpr
    dsimp [B] at h
    linarith
  apply convexOn_of_slope_mono_adjacent convex_univ
  intro x y z _ _ hxy hyz
  simpa only [slope_def_field] using (hupper x y hxy).trans (hlower y z hyz)

end
end ShorNonsmooth.Subdiff


namespace ShorNonsmooth.Subdiff
open Set Filter
open scoped Topology RealInnerProductSpace
noncomputable section

theorem shor_dir_line_right {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) (a d : ℝ)
    (hd : HasOneSidedDirDeriv f (x+a • v) v d) :
    HasDerivWithinAt (fun t : ℝ => f (x+t • v)) d (Ioi a) a := by
  have hs : Tendsto (fun t : ℝ => t-a) (𝓝[>] a) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · have hc : Continuous (fun t : ℝ => t-a) := by fun_prop
      simpa only [sub_self] using (hc.continuousAt (x:=a)).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.mpr (show a<t from ht)
  rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi,slope_fun_def_field]
  have h := hd.comp hs
  convert h using 1
  funext t
  have he : x+a • v+(t-a) • v=x+t • v := by module
  simp only [Function.comp_apply]
  rw [he]

theorem shor_dir_line_left {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) (a d : ℝ)
    (hd : HasOneSidedDirDeriv f (x+a • v) (-v) d) :
    HasDerivWithinAt (fun t : ℝ => f (x+t • v)) (-d) (Iio a) a := by
  have hs : Tendsto (fun t : ℝ => a-t) (𝓝[<] a) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · have hc : Continuous (fun t : ℝ => a-t) := by fun_prop
      simpa only [sub_self] using (hc.continuousAt (x:=a)).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sub_pos.mpr (show t<a from ht)
  rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio,slope_fun_def_field]
  have h := hd.neg.comp hs
  convert h using 1
  funext t
  have he : x+a • v+(a-t) • (-v)=x+t • v := by module
  simp only [Function.comp_apply]
  rw [he]
  have he' : a-t=-(t-a) := by ring
  rw [he',div_neg,neg_neg]

theorem shor_dir_criterion_complete {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    ConvexOn ℝ univ f ↔
      ∃ D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ x v,HasOneSidedDirDeriv f x v (D x v)) ∧
          ∀ x v,Monotone (fun t : ℝ => D (x+t • v) v) := by
  constructor
  · intro hc
    have hex : ∀ x v : EuclideanSpace ℝ (Fin n),∃ d,HasOneSidedDirDeriv f x v d :=
      fun x v => shor_direction_exists univ f hc x (by simp) v
    let D := fun x v => (hex x v).choose
    have hD : ∀ x v,HasOneSidedDirDeriv f x v (D x v) := fun x v => (hex x v).choose_spec
    refine ⟨D,hD,?_⟩
    intro x v
    have hline : ConvexOn ℝ univ (fun t : ℝ => f (x+t • v)) := by
      simpa using shor_line_convex_domain univ f hc x v
    have he : (fun t : ℝ => D (x+t • v) v)=
        (fun t : ℝ => derivWithin (fun s : ℝ => f (x+s • v)) (Ioi t) t) := by
      funext t
      exact ((shor_dir_line_right f x v t _ (hD _ _)).derivWithin (uniqueDiffWithinAt_Ioi t)).symm
    rw [he]
    intro a b hab
    exact hline.monotoneOn_rightDeriv (by simp) (by simp) hab
  · rintro ⟨D,hD,hm⟩
    have hline : ∀ x v : EuclideanSpace ℝ (Fin n),
        ConvexOn ℝ univ (fun t : ℝ => f (x+t • v)) := by
      intro x v
      have hcont : Continuous (fun t : ℝ => f (x+t • v)) := by
        apply continuous_iff_continuousAt.mpr
        intro t
        apply continuousAt_iff_continuous_left'_right'.mpr
        exact ⟨(shor_dir_line_left f x v t _ (hD _ _)).continuousWithinAt,
          (shor_dir_line_right f x v t _ (hD _ _)).continuousWithinAt⟩
      exact shor_real_convex_of_right_mono _ _ hcont
        (fun t => shor_dir_line_right f x v t _ (hD _ _)) (hm x v)
    refine ⟨convex_univ,?_⟩
    intro x _ y _ a b ha hb hab
    have h := (hline x (y-x)).2 (mem_univ (0:ℝ)) (mem_univ (1:ℝ)) ha hb hab
    have he : x+b • (y-x)=a • x+b • y := by
      rw [smul_sub]
      have he' : a • x+b • x=x := by rw [← add_smul,hab,one_smul]
      calc x+(b • y-b • x) = (a • x+b • x)+(b • y-b • x) := by rw [he']
        _ = a • x+b • y := by abel
    simpa only [smul_eq_mul,mul_zero,mul_one,zero_add,zero_smul,add_zero,one_smul,
      add_sub_cancel,he] using h

end
end ShorNonsmooth.Subdiff
noncomputable section
open ShorNonsmooth.Subdiff
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    ConvexOn ℝ Set.univ f ↔
      ∃ D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ x η, HasOneSidedDirDeriv f x η (D x η)) ∧
          ∀ x η, Monotone (fun t : ℝ => D (x+t • η) η) :=
  shor_dir_criterion_complete f
end
#print axioms solution
