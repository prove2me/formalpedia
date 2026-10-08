-- Prove2me | solution 1 for StochFictPlay.Potential.restPoints_eq_criticalPoints
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:29:54.485662+00:00
-- url     : https://prove2.me/submissions/0d18cb09-4140-473f-ad9d-474a0db27a24

import Mathlib
import Definitions.Def_StochFictPlay_Potential_ChoiceModel
import Definitions.Def_StochFictPlay_Potential_Dynamics
import Definitions.Def_StochFictPlay_Potential_Game
import Definitions.Def_StochFictPlay_Potential_PotentialGame

set_option autoImplicit false

open StochFictPlay.Potential in
theorem rpcp_planeProj_of_sum {m : ℕ} (w : Fin m → ℝ) (hw : ∑ i, w i = 1) :
    planeProj m w = w := by
  funext i; simp [planeProj, hw]

open StochFictPlay.Potential in
theorem rpcp_isOpen_U (m : ℕ) : IsOpen {w : Fin m → ℝ | ∀ i, 0 < planeProj m w i} := by
  have : {w : Fin m → ℝ | ∀ i, 0 < planeProj m w i} = ⋂ i, {w | 0 < planeProj m w i} := by
    ext; simp
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (by unfold planeProj; fun_prop)

open StochFictPlay.Potential in
theorem rpcp_mem_U {m : ℕ} {y : Fin m → ℝ} (hy : y ∈ openSimplex m) :
    y ∈ {w : Fin m → ℝ | ∀ i, 0 < planeProj m w i} := by
  show ∀ i, 0 < planeProj m y i
  rw [rpcp_planeProj_of_sum y hy.2]; exact hy.1

theorem rpcp_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a z : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => a + s • z) z t := by
  simpa using ((hasDerivAt_id t).smul_const z).const_add a

open StochFictPlay.Potential in
theorem rpcp_diff {m : ℕ} {V : (Fin m → ℝ) → ℝ} (hV : IsAdmissible V) {y : Fin m → ℝ}
    (hy : y ∈ {w : Fin m → ℝ | ∀ i, 0 < planeProj m w i}) :
    DifferentiableAt ℝ (V ∘ planeProj m) y :=
  (hV.1.differentiableOn (by norm_num)).differentiableAt ((rpcp_isOpen_U m).mem_nhds hy)

open StochFictPlay.Potential in
theorem rpcp_diff2 {m : ℕ} {V : (Fin m → ℝ) → ℝ} (hV : IsAdmissible V) {y : Fin m → ℝ}
    (hy : y ∈ {w : Fin m → ℝ | ∀ i, 0 < planeProj m w i}) :
    DifferentiableAt ℝ (fderiv ℝ (V ∘ planeProj m)) y := by
  have h1 := hV.1.fderiv_of_isOpen (rpcp_isOpen_U m) (m := 1) (by norm_num)
  exact (h1.differentiableOn (by norm_num)).differentiableAt ((rpcp_isOpen_U m).mem_nhds hy)

-- First-order condition at the perturbed argmax.
open StochFictPlay.Potential in
theorem rpcp_foc {m : ℕ} {V : (Fin m → ℝ) → ℝ} {Ct : (Fin m → ℝ) → (Fin m → ℝ)}
    (hV : IsAdmissible V) (hCt : IsPerturbedArgmax V Ct) (π z : Fin m → ℝ)
    (hz : ∑ i, z i = 0) :
    z ⬝ᵥ π - fderiv ℝ (V ∘ planeProj m) (Ct π) z = 0 := by
  set y := Ct π with hydef
  have hy : y ∈ openSimplex m := (hCt π).1
  have hd : DifferentiableAt ℝ (V ∘ planeProj m) (y + (0:ℝ) • z) := by
    simpa using rpcp_diff hV (rpcp_mem_U hy)
  have hg := hd.hasFDerivAt.comp_hasDerivAt (0:ℝ) (rpcp_line y z 0)
  have hdot : HasDerivAt (fun h : ℝ => (y + h • z) ⬝ᵥ π) (z ⬝ᵥ π) 0 := by
    have : (fun h : ℝ => (y + h • z) ⬝ᵥ π) = fun h => y ⬝ᵥ π + h * (z ⬝ᵥ π) := by
      funext h; simp [add_dotProduct, smul_dotProduct]
    rw [this]
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (z ⬝ᵥ π)).const_add (y ⬝ᵥ π)
  have hφ := hdot.sub hg
  simp only [zero_smul, add_zero] at hφ
  have hPeq : ∀ w ∈ openSimplex m, (V ∘ planeProj m) w = V w := fun w hw => by
    simp [Function.comp, rpcp_planeProj_of_sum w hw.2]
  refine IsLocalMax.hasDerivAt_eq_zero ?_ hφ
  have hev : ∀ᶠ h in nhds (0:ℝ), ∀ i, 0 < y i + h * z i := Filter.eventually_all.2 fun i => by
    have hc : ContinuousAt (fun h : ℝ => y i + h * z i) 0 := by fun_prop
    exact continuousAt_const.eventually_lt hc (by simpa using hy.1 i)
  filter_upwards [hev] with h hh
  have hmem : y + h • z ∈ openSimplex m :=
    ⟨fun i => by simpa using hh i, by
      simp [Finset.sum_add_distrib, ← Finset.mul_sum, hz, hy.2]⟩
  show (y + h • z) ⬝ᵥ π - (V ∘ planeProj m) (y + h • z) ≤
    (y + (0:ℝ) • z) ⬝ᵥ π - (V ∘ planeProj m) (y + (0:ℝ) • z)
  rw [zero_smul, add_zero, hPeq _ hmem, hPeq _ hy]
  by_cases hyy : y + h • z = y
  · rw [hyy]
  · exact ((hCt π).2 _ hmem hyy).le

-- A tangent-critical point of y ↦ y ⬝ π - V y is the perturbed argmax (concavity).
open StochFictPlay.Potential in
theorem rpcp_argmax_of_crit {m : ℕ} {V : (Fin m → ℝ) → ℝ} {Ct : (Fin m → ℝ) → (Fin m → ℝ)}
    (hV : IsAdmissible V) (hCt : IsPerturbedArgmax V Ct) (π y0 : Fin m → ℝ)
    (hy0 : y0 ∈ openSimplex m)
    (hcrit : ∀ z : Fin m → ℝ, ∑ i, z i = 0 → z ⬝ᵥ π = fderiv ℝ (V ∘ planeProj m) y0 z) :
    Ct π = y0 := by
  have hPeq : ∀ w ∈ openSimplex m, (V ∘ planeProj m) w = V w := fun w hw => by
    simp [Function.comp, rpcp_planeProj_of_sum w hw.2]
  have key : ∀ y ∈ openSimplex m, y ⬝ᵥ π - V y ≤ y0 ⬝ᵥ π - V y0 := by
    intro y hy
    set g := V ∘ planeProj m with hgdef
    set z := y - y0 with hzdef
    have hz : ∑ i, z i = 0 := by simp [hzdef, Finset.sum_sub_distrib, hy.2, hy0.2]
    have hw : ∀ t ∈ Set.Icc (0:ℝ) 1, y0 + t • z ∈ openSimplex m := by
      intro t ⟨ht0, ht1⟩
      refine ⟨fun i => ?_, by simp [Finset.sum_add_distrib, ← Finset.mul_sum, hz, hy0.2]⟩
      have ha := hy0.1 i
      have hb := hy.1 i
      simp only [hzdef, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rcases le_total (y0 i) (y i) with hab | hab
      · nlinarith [mul_nonneg ht0 (sub_nonneg.2 hab)]
      · nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hab)]
    have hU : ∀ t ∈ Set.Icc (0:ℝ) 1,
        y0 + t • z ∈ {w : Fin m → ℝ | ∀ i, 0 < planeProj m w i} :=
      fun t ht => rpcp_mem_U (hw t ht)
    have hψ' : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt (fun s : ℝ => fderiv ℝ g (y0 + s • z) z)
        (fderiv ℝ (fderiv ℝ g) (y0 + t • z) z z) t := by
      intro t ht
      have h1 := HasFDerivAt.comp_hasDerivAt (l := fderiv ℝ g) (f := fun s : ℝ => y0 + s • z) t
        (rpcp_diff2 hV (hU t ht)).hasFDerivAt (rpcp_line y0 z t)
      have h2 := h1.clm_apply (hasDerivAt_const t z)
      simpa using h2
    have hψ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt (fun s : ℝ => g (y0 + s • z))
        (fderiv ℝ g (y0 + t • z) z) t := fun t ht =>
      HasFDerivAt.comp_hasDerivAt (l := g) (f := fun s : ℝ => y0 + s • z) t
        (rpcp_diff hV (hU t ht)).hasFDerivAt (rpcp_line y0 z t)
    have hψ''nn : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ fderiv ℝ (fderiv ℝ g) (y0 + t • z) z z := by
      intro t ht
      by_cases hz0 : z = 0
      · simp [hz0]
      · exact (hV.2.1 _ (hw t ht) z hz hz0).le
    have hmono : MonotoneOn (fun s : ℝ => fderiv ℝ g (y0 + s • z) z) (Set.Icc 0 1) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
        (f' := fun t => fderiv ℝ (fderiv ℝ g) (y0 + t • z) z z)
      · exact fun t ht => (hψ' t ht).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (hψ' t (Set.Ioo_subset_Icc_self ht)).hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact hψ''nn t (Set.Ioo_subset_Icc_self ht)
    have hΦ : ∀ t ∈ Set.Icc (0:ℝ) 1,
        HasDerivAt (fun s : ℝ => (y0 + s • z) ⬝ᵥ π - g (y0 + s • z))
          (z ⬝ᵥ π - fderiv ℝ g (y0 + t • z) z) t := by
      intro t ht
      have hdot : HasDerivAt (fun h : ℝ => (y0 + h • z) ⬝ᵥ π) (z ⬝ᵥ π) t := by
        have : (fun h : ℝ => (y0 + h • z) ⬝ᵥ π) = fun h => y0 ⬝ᵥ π + h * (z ⬝ᵥ π) := by
          funext h; simp [add_dotProduct, smul_dotProduct]
        rw [this]
        simpa using ((hasDerivAt_id t).mul_const (z ⬝ᵥ π)).const_add (y0 ⬝ᵥ π)
      exact hdot.sub (hψ t ht)
    have hanti : AntitoneOn (fun s : ℝ => (y0 + s • z) ⬝ᵥ π - g (y0 + s • z))
        (Set.Icc 0 1) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
        (f' := fun t => z ⬝ᵥ π - fderiv ℝ g (y0 + t • z) z)
      · exact fun t ht => (hΦ t ht).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (hΦ t (Set.Ioo_subset_Icc_self ht)).hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have h1 := hmono (Set.left_mem_Icc.2 zero_le_one) (Set.Ioo_subset_Icc_self ht) ht.1.le
        have h0 := hcrit z hz
        simp only [zero_smul, add_zero] at h1
        linarith
    have h01 := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
      zero_le_one
    have hy1 : y0 + (1:ℝ) • z = y := by simp [hzdef]
    simp only [zero_smul, add_zero, hy1] at h01
    rw [hPeq _ hy, hPeq _ hy0] at h01
    exact h01
  by_contra hne
  have h1 := (hCt π).2 y0 hy0 (Ne.symm hne)
  have h2 := key _ (hCt π).1
  linarith

-- The polynomial part of Π differentiates to ∑_α θ^α ⬝ U^α(x) in a potential game.
open StochFictPlay.Potential in
theorem rpcp_poly_identity {p : ℕ} {n : Fin p → ℕ} (u : (α : Fin p) → Profile n → ℝ)
    (hpot : IsPotentialGame u) (α₀ : Fin p) (x θ : Mixed n) :
    ∑ α, θ α ⬝ᵥ payoffVec u x α =
      ∑ s : Profile n, u α₀ s * ∑ α, (∏ β ∈ Finset.univ.erase α, x β (s β)) * θ α (s α) := by
  have h1 : ∀ α, θ α ⬝ᵥ payoffVec u x α =
      ∑ s : Profile n, θ α (s α) * (u α s * ∏ β ∈ Finset.univ.erase α, x β (s β)) := by
    intro α
    simp only [dotProduct, payoffVec, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp
  simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun α _ => ?_
  rw [hpot α α₀ s]; ring

open StochFictPlay.Potential in
theorem rpcp_deriv {p : ℕ} {n : Fin p → ℕ} (u : (α : Fin p) → Profile n → ℝ)
    (hpot : IsPotentialGame u) (V : (α : Fin p) → (Fin (n α) → ℝ) → ℝ)
    (hV : ∀ α, IsAdmissible (V α)) (α₀ : Fin p) (x θ : Mixed n)
    (hx : x ∈ interiorProfiles n) (hθ : ∀ α, ∑ i, θ α i = 0) :
    HasDerivAt (fun h : ℝ => potentialFn V u α₀ (x + h • θ))
      (∑ α, (θ α ⬝ᵥ payoffVec u x α -
        fderiv ℝ (V α ∘ planeProj (n α)) (x α) (θ α))) 0 := by
  have h1 : HasDerivAt (fun h : ℝ => ∑ s : Profile n, u α₀ s * ∏ α, (x + h • θ) α (s α))
      (∑ s : Profile n, u α₀ s *
        ∑ α, (∏ β ∈ Finset.univ.erase α, x β (s β)) * θ α (s α)) 0 := by
    apply HasDerivAt.fun_sum
    intro s _
    apply HasDerivAt.const_mul
    have := HasDerivAt.fun_finsetProd (u := Finset.univ)
      (f := fun α (h : ℝ) => x α (s α) + h * θ α (s α)) (f' := fun α => θ α (s α)) (x := 0)
      (fun α _ => by
        simpa using ((hasDerivAt_id (0:ℝ)).mul_const (θ α (s α))).const_add (x α (s α)))
    simpa [smul_eq_mul] using this
  have h2 : ∀ α, HasDerivAt (fun h : ℝ => V α ((x + h • θ) α))
      (fderiv ℝ (V α ∘ planeProj (n α)) (x α) (θ α)) 0 := by
    intro α
    have hfun : (fun h : ℝ => V α ((x + h • θ) α)) =
        (V α ∘ planeProj (n α)) ∘ (fun h : ℝ => x α + h • θ α) := by
      funext h
      show V α (x α + h • θ α) = V α (planeProj (n α) (x α + h • θ α))
      rw [rpcp_planeProj_of_sum _ (by
        simp [Finset.sum_add_distrib, ← Finset.mul_sum, (hx α).2, hθ α])]
    rw [hfun]
    have hd : DifferentiableAt ℝ (V α ∘ planeProj (n α)) (x α + (0:ℝ) • θ α) := by
      simpa using rpcp_diff (hV α) (rpcp_mem_U (hx α))
    simpa using hd.hasFDerivAt.comp_hasDerivAt (0:ℝ) (rpcp_line (x α) (θ α) 0)
  have h3 := h1.fun_sub (HasDerivAt.fun_sum (u := Finset.univ) fun α _ => h2 α)
  rw [Finset.sum_sub_distrib, rpcp_poly_identity u hpot α₀ x θ]
  exact h3

open StochFictPlay.Potential in
theorem solution (p : ℕ) (hp : 2 ≤ p) (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (hpot : IsPotentialGame u)
    (V : (α : Fin p) → (Fin (n α) → ℝ) → ℝ)
    (Ct : (α : Fin p) → (Fin (n α) → ℝ) → (Fin (n α) → ℝ))
    (hV : ∀ α, IsAdmissible (V α)) (hCt : ∀ α, IsPerturbedArgmax (V α) (Ct α)) :
    restPoints (pvField Ct u) (mixedProfiles n) =
      {x | x ∈ interiorProfiles n ∧ IsTangentCritical (potentialFn V u ⟨0, by omega⟩) x} := by
  ext x
  constructor
  · rintro ⟨_, hrest⟩
    have hx : ∀ α, Ct α (payoffVec u x α) = x α := fun α => by
      have := congrFun hrest α
      simpa [pvField, sub_eq_zero] using this
    have hint : x ∈ interiorProfiles n := fun α => by
      rw [← hx α]; exact (hCt α _).1
    refine ⟨hint, fun θ hθ => ?_⟩
    have hd := rpcp_deriv u hpot V hV ⟨0, by omega⟩ x θ hint hθ
    convert hd using 1
    symm
    refine Finset.sum_eq_zero fun α _ => ?_
    have := rpcp_foc (hV α) (hCt α) (payoffVec u x α) (θ α) (hθ α)
    rwa [hx α] at this
  · rintro ⟨hint, hcrit⟩
    refine ⟨fun α => ⟨fun i => ((hint α).1 i).le, (hint α).2⟩, ?_⟩
    funext α
    show Ct α (payoffVec u x α) - x α = 0
    rw [sub_eq_zero]
    refine rpcp_argmax_of_crit (hV α) (hCt α) _ _ (hint α) fun z hz => ?_
    let θ : Mixed n := Pi.single α z
    have hθ : ∀ β, ∑ i, θ β i = 0 := by
      intro β
      by_cases hβ : β = α
      · subst hβ; simp [θ, hz]
      · simp [θ, Pi.single_eq_of_ne hβ]
    have hd := rpcp_deriv u hpot V hV ⟨0, by omega⟩ x θ hint hθ
    have h0 := (hcrit θ hθ).unique hd
    rw [Finset.sum_eq_single α (fun β _ hβ => by simp [θ, Pi.single_eq_of_ne hβ])
      (by simp)] at h0
    simp only [θ, Pi.single_eq_same] at h0
    linarith
