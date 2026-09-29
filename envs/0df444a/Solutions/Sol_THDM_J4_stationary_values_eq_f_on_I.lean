-- Prove2me | solution 1 for THDM.J4_stationary_values_eq_f_on_I
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:33:08.282+00:00
-- url     : https://prove2.me/submissions/d284bf52-2581-4ec5-adfe-ac5d96ffecb1

import Mathlib
import Definitions.Def_THDM_stationary

set_option autoImplicit false

open scoped BigOperators
open Matrix Filter Topology

noncomputable def thdmPhi (eta00 : ℝ) (eta d : Fin 3 → ℝ) (u : ℝ) : ℝ :=
  u + eta00 - ∑ i, eta i * ((d i - u)⁻¹ * eta i)

noncomputable def thdmPsi (eta d : Fin 3 → ℝ) (u : ℝ) : ℝ :=
  1 - ∑ i, eta i * (((d i - u)⁻¹ * (d i - u)⁻¹) * eta i)

noncomputable def thdmGam (xi0 : ℝ) (xi eta d : Fin 3 → ℝ) (u : ℝ) : ℝ :=
  xi0 - ∑ i, xi i * ((d i - u)⁻¹ * eta i)

open THDM in
lemma thdm_quad3_eq (E : Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ) :
    quad3 E x y = x ⬝ᵥ (E *ᵥ y) := by
  simp only [quad3, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

lemma thdm_diag_sub (d : Fin 3 → ℝ) (u : ℝ) :
    diagonal d - u • (1 : Matrix (Fin 3) (Fin 3) ℝ) = diagonal (fun i => d i - u) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [h, Matrix.one_apply_ne h]

open THDM in
lemma thdm_reg_diag (d : Fin 3 → ℝ) (u : ℝ) :
    Reg (diagonal d) u ↔ ∀ i, d i ≠ u := by
  rw [Reg, thdm_diag_sub, det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  simp [sub_ne_zero]

lemma thdm_inv_diag (v : Fin 3 → ℝ) (hv : ∀ i, v i ≠ 0) :
    (diagonal v)⁻¹ = diagonal (fun i => (v i)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [diagonal_mul_diagonal]
  have : (fun i => (v i)⁻¹ * v i) = fun _ => (1:ℝ) := funext fun i => inv_mul_cancel₀ (hv i)
  rw [this, diagonal_one]

open THDM in
lemma thdm_resolv_diag (d : Fin 3 → ℝ) (u : ℝ) (h : Reg (diagonal d) u) :
    resolv (diagonal d) u = diagonal (fun i => (d i - u)⁻¹) := by
  rw [resolv, thdm_diag_sub, thdm_inv_diag]
  intro i; exact sub_ne_zero.mpr (((thdm_reg_diag d u).1 h) i)

open THDM in
lemma thdm_fFun_diag (eta00 : ℝ) (eta d : Fin 3 → ℝ) (u : ℝ) (h : Reg (diagonal d) u) :
    fFun eta00 eta (diagonal d) u = thdmPhi eta00 eta d u := by
  simp only [fFun, thdm_resolv_diag d u h, thdmPhi, dot3, mulVec_diagonal]

open THDM in
lemma thdm_fPrime_diag (eta d : Fin 3 → ℝ) (u : ℝ) (h : Reg (diagonal d) u) :
    fPrime eta (diagonal d) u = thdmPsi eta d u := by
  simp only [fPrime, thdm_resolv_diag d u h, thdmPsi, dot3, diagonal_mul_diagonal, mulVec_diagonal]

open THDM in
lemma thdm_gFun_diag (xi0 : ℝ) (xi eta d : Fin 3 → ℝ) (u : ℝ) (h : Reg (diagonal d) u) :
    gFun xi0 xi eta (diagonal d) u = thdmGam xi0 xi eta d u := by
  simp only [gFun, thdm_resolv_diag d u h, thdmGam, dot3, mulVec_diagonal]

open THDM in
lemma thdm_ev_reg (d : Fin 3 → ℝ) (u : ℝ) : ∀ᶠ x in 𝓝[≠] u, Reg (diagonal d) x := by
  simp_rw [thdm_reg_diag]
  rw [Filter.eventually_all]
  intro i
  by_cases h : d i = u
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    rw [h]; exact fun h' => hx h'.symm
  · have : ∀ᶠ x in 𝓝 u, x ≠ d i := eventually_ne_nhds (Ne.symm h)
    filter_upwards [nhdsWithin_le_nhds this] with x hx
    exact Ne.symm hx

lemma thdm_inv_cont (a u : ℝ) (h : a ≠ u) : ContinuousAt (fun x : ℝ => (a - x)⁻¹) u :=
  (continuousAt_const.sub continuousAt_id).inv₀ (sub_ne_zero.mpr h)

lemma thdm_cont_Phi (eta00 : ℝ) (eta d : Fin 3 → ℝ) (u : ℝ) (hc : ∀ i, d i = u → eta i = 0) :
    ContinuousAt (thdmPhi eta00 eta d) u := by
  show ContinuousAt (fun x => x + eta00 - ∑ i, eta i * ((d i - x)⁻¹ * eta i)) u
  apply ContinuousAt.sub (by fun_prop)
  refine tendsto_finsetSum _ (fun i _ => ?_)
  by_cases h : d i = u
  · simp only [hc i h, zero_mul, mul_zero]; exact continuousAt_const
  · exact continuousAt_const.mul ((thdm_inv_cont _ _ h).mul continuousAt_const)

lemma thdm_cont_Psi (eta d : Fin 3 → ℝ) (u : ℝ) (hc : ∀ i, d i = u → eta i = 0) :
    ContinuousAt (thdmPsi eta d) u := by
  show ContinuousAt (fun x => 1 - ∑ i, eta i * (((d i - x)⁻¹ * (d i - x)⁻¹) * eta i)) u
  apply ContinuousAt.sub continuousAt_const
  refine tendsto_finsetSum _ (fun i _ => ?_)
  by_cases h : d i = u
  · simp only [hc i h, zero_mul, mul_zero]; exact continuousAt_const
  · exact continuousAt_const.mul
      (((thdm_inv_cont _ _ h).mul (thdm_inv_cont _ _ h)).mul continuousAt_const)

lemma thdm_cont_Gam (xi0 : ℝ) (xi eta d : Fin 3 → ℝ) (u : ℝ) (hc : ∀ i, d i = u → eta i = 0) :
    ContinuousAt (thdmGam xi0 xi eta d) u := by
  show ContinuousAt (fun x => xi0 - ∑ i, xi i * ((d i - x)⁻¹ * eta i)) u
  apply ContinuousAt.sub continuousAt_const
  refine tendsto_finsetSum _ (fun i _ => ?_)
  by_cases h : d i = u
  · simp only [hc i h, mul_zero]; exact continuousAt_const
  · exact continuousAt_const.mul ((thdm_inv_cont _ _ h).mul continuousAt_const)

open THDM in
lemma thdm_punctLim_eq (F : ℝ → ℝ) (u L : ℝ) (h : Tendsto F (𝓝[≠] u) (𝓝 L)) :
    punctLim F u = L := by
  have hex : ∃ L : ℝ, Tendsto F (nhdsWithin u {u}ᶜ) (nhds L) := ⟨L, h⟩
  rw [punctLim, dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec h

open THDM in
lemma thdm_fVal_diag (eta00 : ℝ) (eta d : Fin 3 → ℝ) (u : ℝ) (hc : ∀ i, d i = u → eta i = 0) :
    fVal eta00 eta (diagonal d) u = thdmPhi eta00 eta d u := by
  unfold fVal
  split_ifs with h
  · exact thdm_fFun_diag _ _ _ _ h
  · apply thdm_punctLim_eq
    refine ((thdm_cont_Phi eta00 eta d u hc).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [thdm_ev_reg d u] with x hx
    exact (thdm_fFun_diag _ _ _ _ hx).symm

open THDM in
lemma thdm_fPrimeVal_diag (eta d : Fin 3 → ℝ) (u : ℝ) (hc : ∀ i, d i = u → eta i = 0) :
    fPrimeVal eta (diagonal d) u = thdmPsi eta d u := by
  unfold fPrimeVal
  split_ifs with h
  · exact thdm_fPrime_diag _ _ _ h
  · apply thdm_punctLim_eq
    refine ((thdm_cont_Psi eta d u hc).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [thdm_ev_reg d u] with x hx
    exact (thdm_fPrime_diag _ _ _ hx).symm

open THDM in
lemma thdm_gVal_diag (xi0 : ℝ) (xi eta d : Fin 3 → ℝ) (u : ℝ) (hc : ∀ i, d i = u → eta i = 0) :
    gVal xi0 xi eta (diagonal d) u = thdmGam xi0 xi eta d u := by
  unfold gVal
  split_ifs with h
  · exact thdm_gFun_diag _ _ _ _ _ h
  · apply thdm_punctLim_eq
    refine ((thdm_cont_Gam xi0 xi eta d u hc).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [thdm_ev_reg d u] with x hx
    exact (thdm_gFun_diag _ _ _ _ _ hx).symm

open THDM in
lemma thdm_tendsto_fFun (eta00 : ℝ) (eta d : Fin 3 → ℝ) (u : ℝ) (hc : ∀ i, d i = u → eta i = 0) :
    Tendsto (fFun eta00 eta (diagonal d)) (𝓝[≠] u) (𝓝 (thdmPhi eta00 eta d u)) := by
  refine ((thdm_cont_Phi eta00 eta d u hc).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [thdm_ev_reg d u] with x hx
  exact (thdm_fFun_diag _ _ _ _ hx).symm

open THDM in
lemma thdm_tendsto_fPrime (eta d : Fin 3 → ℝ) (u : ℝ) (hc : ∀ i, d i = u → eta i = 0) :
    Tendsto (fPrime eta (diagonal d)) (𝓝[≠] u) (𝓝 (thdmPsi eta d u)) := by
  refine ((thdm_cont_Psi eta d u hc).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [thdm_ev_reg d u] with x hx
  exact (thdm_fPrime_diag _ _ _ hx).symm

open THDM in
lemma thdm_compat_of_tendsto (eta00 : ℝ) (eta d : Fin 3 → ℝ) (u L : ℝ)
    (h : Tendsto (fFun eta00 eta (diagonal d)) (𝓝[≠] u) (𝓝 L)) :
    ∀ i, d i = u → eta i = 0 := by
  set H : ℝ → ℝ := fun x => (x - u) * (x + eta00) -
    ∑ i, eta i * eta i * (if d i = u then -1 else (x - u) * (d i - x)⁻¹) with hH
  have hHc : ContinuousAt H u := by
    apply ContinuousAt.sub (by fun_prop)
    refine tendsto_finsetSum _ (fun i _ => ?_)
    by_cases hi : d i = u
    · simp only [hi, if_true]; exact continuousAt_const
    · simp only [hi, if_false]
      exact continuousAt_const.mul
        ((continuousAt_id.sub continuousAt_const).mul (thdm_inv_cont _ _ hi))
  have hlim1 : Tendsto H (𝓝[≠] u) (𝓝 (H u)) := hHc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto H (𝓝[≠] u) (𝓝 ((u - u) * L)) := by
    have hx : Tendsto (fun x : ℝ => x - u) (𝓝[≠] u) (𝓝 (u - u)) :=
      ((continuousAt_id.sub continuousAt_const).tendsto).mono_left nhdsWithin_le_nhds
    refine (hx.mul h).congr' ?_
    filter_upwards [thdm_ev_reg d u, self_mem_nhdsWithin] with x hx hxu
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hxu
    rw [thdm_fFun_diag _ _ _ _ hx]
    simp only [thdmPhi, hH]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rw [hi]
      have : u - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxu)
      field_simp
      ring
    · ring
  have heq := tendsto_nhds_unique hlim1 hlim2
  have hHu : H u = ∑ i, (if d i = u then eta i * eta i else 0) := by
    simp only [hH, sub_self, zero_mul, zero_sub, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  rw [hHu, sub_self, zero_mul] at heq
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by
    split_ifs
    · exact mul_self_nonneg (eta i)
    · exact le_refl (0:ℝ))).1 heq
  intro i hi
  have := hall i (Finset.mem_univ i)
  rw [if_pos hi] at this
  exact mul_self_eq_zero.mp this

open THDM in
lemma thdm_quad3_dot (E : Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ) :
    quad3 E x y = dot3 x (E *ᵥ y) := by
  simp only [quad3, dot3, mulVec, dotProduct, Finset.mul_sum, mul_assoc]

open THDM in
lemma thdm_J4_diag_eq (eta00 : ℝ) (eta d k : Fin 3 → ℝ) (u : ℝ)
    (hk : ∀ i, (d i - u) * k i = -eta i) :
    J4 eta00 eta (diagonal d) k = thdmPhi eta00 eta d u + u * (dot3 k k - 1) := by
  have hpt : ∀ i, 2 * (eta i * k i) + k i * (d i * k i) =
      u * (k i * k i) - eta i * ((d i - u)⁻¹ * eta i) := by
    intro i
    have he : eta i = -((d i - u) * k i) := by rw [hk i]; ring
    rw [he]
    by_cases h : d i = u
    · rw [h, sub_self, _root_.inv_zero]; ring
    · have : d i - u ≠ 0 := sub_ne_zero.mpr h
      field_simp
      ring
  rw [J4, thdm_quad3_dot, thdmPhi]
  simp only [dot3, mulVec_diagonal, Fin.sum_univ_three]
  linear_combination hpt 0 + hpt 1 + hpt 2

lemma thdm_Psi_eq (eta d k : Fin 3 → ℝ) (u : ℝ) (hk : ∀ i, (d i - u) * k i = -eta i) :
    thdmPsi eta d u = 1 - ∑ i, (if d i = u then 0 else k i * k i) := by
  unfold thdmPsi
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : eta i = -((d i - u) * k i) := by rw [hk i]; ring
  rw [he]
  split_ifs with h
  · rw [h, sub_self, _root_.inv_zero]; ring
  · have : d i - u ≠ 0 := sub_ne_zero.mpr h
    field_simp

open THDM in
lemma thdm_J2_eq (xi0 : ℝ) (xi eta d k : Fin 3 → ℝ) (u : ℝ)
    (hk : ∀ i, (d i - u) * k i = -eta i) :
    J2 xi0 xi k = thdmGam xi0 xi eta d u + ∑ i, (if d i = u then xi i * k i else 0) := by
  have hpt : ∀ i, xi i * k i =
      -(xi i * ((d i - u)⁻¹ * eta i)) + (if d i = u then xi i * k i else 0) := by
    intro i
    have he : eta i = -((d i - u) * k i) := by rw [hk i]; ring
    split_ifs with h
    · rw [he, h, sub_self, _root_.inv_zero]; ring
    · rw [he]
      have : d i - u ≠ 0 := sub_ne_zero.mpr h
      field_simp
      ring
  rw [J2, thdmGam]
  simp only [dot3, Fin.sum_univ_three]
  linear_combination hpt 0 + hpt 1 + hpt 2

noncomputable def thdmK0 (eta d : Fin 3 → ℝ) (u : ℝ) : Fin 3 → ℝ :=
  fun i => -((d i - u)⁻¹ * eta i)

lemma thdm_K0_eq (eta d : Fin 3 → ℝ) (u : ℝ) (hc : ∀ i, d i = u → eta i = 0) (i : Fin 3) :
    (d i - u) * thdmK0 eta d u i = -eta i := by
  unfold thdmK0
  by_cases h : d i = u
  · rw [hc i h, h, sub_self]; ring
  · have : d i - u ≠ 0 := sub_ne_zero.mpr h
    field_simp

lemma thdm_K0_zero (eta d : Fin 3 → ℝ) (u : ℝ) (i : Fin 3) (h : d i = u) :
    thdmK0 eta d u i = 0 := by
  unfold thdmK0; rw [h, sub_self, _root_.inv_zero]; ring

open THDM in
lemma thdm_K0_sq (eta d : Fin 3 → ℝ) (u : ℝ) :
    dot3 (thdmK0 eta d u) (thdmK0 eta d u) = 1 - thdmPsi eta d u := by
  unfold thdmPsi dot3 thdmK0
  rw [sub_sub_cancel]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma thdm_lin (d eta : Fin 3 → ℝ) (u : ℝ) (k : Fin 3 → ℝ) :
    (diagonal d - u • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ k = -eta ↔
      ∀ i, (d i - u) * k i = -eta i := by
  rw [thdm_diag_sub]
  constructor
  · intro h i
    have := congrFun h i
    simpa [mulVec_diagonal] using this
  · intro h
    funext i
    simp [mulVec_diagonal, h i]

lemma thdm_lin0 (d eta : Fin 3 → ℝ) (k : Fin 3 → ℝ) :
    diagonal d *ᵥ k = -eta ↔ ∀ i, (d i - 0) * k i = -eta i := by
  rw [← thdm_lin d eta 0 k, zero_smul, sub_zero]

open THDM in
lemma thdm_J4_diag (eta00 : ℝ) (eta d : Fin 3 → ℝ) :
    {v : ℝ | ∃ k : Fin 3 → ℝ,
        ((dot3 k k < 1 ∧ diagonal d *ᵥ k = -eta) ∨
         (dot3 k k = 1 ∧ ∃ u : ℝ, (diagonal d - u • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ k = -eta)) ∧
        v = J4 eta00 eta (diagonal d) k}
      = (fun u => fVal eta00 eta (diagonal d) u) '' (Iset eta00 eta (diagonal d)) := by
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_image, Iset, Set.mem_union]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨u, hku, hnorm⟩ : ∃ u, (∀ i, (d i - u) * k i = -eta i) ∧
        ((u = 0 ∧ dot3 k k < 1) ∨ dot3 k k = 1) := by
      rcases hk with ⟨h1, h2⟩ | ⟨h1, u, h2⟩
      · exact ⟨0, (thdm_lin0 d eta k).1 h2, Or.inl ⟨rfl, h1⟩⟩
      · exact ⟨u, (thdm_lin d eta u k).1 h2, Or.inr h1⟩
    have hc : ∀ i, d i = u → eta i = 0 := by
      intro i hi
      have := hku i
      rw [hi, sub_self, zero_mul] at this
      linarith
    have hJ : J4 eta00 eta (diagonal d) k = thdmPhi eta00 eta d u := by
      rw [thdm_J4_diag_eq eta00 eta d k u hku]
      rcases hnorm with ⟨rfl, _⟩ | h1
      · ring
      · rw [h1]; ring
    have hPsi := thdm_Psi_eq eta d k u hku
    have hle : ∑ i, (if d i = u then 0 else k i * k i) ≤ dot3 k k := by
      unfold dot3
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact mul_self_nonneg _
      · exact le_refl _
    refine ⟨u, ?_, by rw [thdm_fVal_diag eta00 eta d u hc, hJ]⟩
    by_cases hR : Reg (diagonal d) u
    · have hR' := (thdm_reg_diag d u).1 hR
      have hsum : ∑ i, (if d i = u then 0 else k i * k i) = dot3 k k := by
        unfold dot3
        apply Finset.sum_congr rfl
        intro i _
        rw [if_neg (hR' i)]
      rcases hnorm with ⟨rfl, h1⟩ | h1
      · left; right
        refine ⟨rfl, hR, ?_⟩
        rw [thdm_fPrime_diag eta d 0 hR, hPsi, hsum]
        linarith
      · left; left
        refine ⟨hR, ?_⟩
        rw [thdm_fPrime_diag eta d u hR, hPsi, hsum, h1]
        ring
    · right
      refine ⟨hR, ⟨_, thdm_tendsto_fFun eta00 eta d u hc⟩,
        ⟨_, thdm_tendsto_fPrime eta d u hc⟩, ?_⟩
      rw [thdm_fPrimeVal_diag eta d u hc, hPsi]
      have : dot3 k k ≤ 1 := by rcases hnorm with ⟨_, h⟩ | h <;> linarith
      linarith
  · rintro ⟨u, hu, rfl⟩
    rcases hu with (⟨hR, hP⟩ | ⟨rfl, hR, hP⟩) | ⟨hR, ⟨L, hL⟩, _, hPV⟩
    · have hR' := (thdm_reg_diag d u).1 hR
      have hc : ∀ i, d i = u → eta i = 0 := fun i hi => absurd hi (hR' i)
      refine ⟨thdmK0 eta d u, Or.inr ⟨?_, u, (thdm_lin d eta u _).2 (thdm_K0_eq eta d u hc)⟩, ?_⟩
      · rw [thdm_K0_sq, ← thdm_fPrime_diag eta d u hR, hP]; ring
      · rw [thdm_fVal_diag eta00 eta d u hc,
          thdm_J4_diag_eq eta00 eta d _ u (thdm_K0_eq eta d u hc), thdm_K0_sq,
          ← thdm_fPrime_diag eta d u hR, hP]
        ring
    · have hR' := (thdm_reg_diag d 0).1 hR
      have hc : ∀ i, d i = 0 → eta i = 0 := fun i hi => absurd hi (hR' i)
      refine ⟨thdmK0 eta d 0, Or.inl ⟨?_, (thdm_lin0 d eta _).2 (thdm_K0_eq eta d 0 hc)⟩, ?_⟩
      · rw [thdm_K0_sq, ← thdm_fPrime_diag eta d 0 hR]; linarith
      · rw [thdm_fVal_diag eta00 eta d 0 hc,
          thdm_J4_diag_eq eta00 eta d _ 0 (thdm_K0_eq eta d 0 hc)]
        ring
    · have hc := thdm_compat_of_tendsto eta00 eta d u L hL
      rw [thdm_fPrimeVal_diag eta d u hc] at hPV
      obtain ⟨j, hj⟩ : ∃ j, d j = u := by
        by_contra hne
        push_neg at hne
        exact hR ((thdm_reg_diag d u).2 hne)
      set s := Real.sqrt (thdmPsi eta d u) with hs
      set k : Fin 3 → ℝ := fun i => thdmK0 eta d u i + (if i = j then s else 0) with hkdef
      have hk : ∀ i, (d i - u) * k i = -eta i := by
        intro i
        simp only [hkdef]
        rw [mul_add, thdm_K0_eq eta d u hc]
        split_ifs with h
        · rw [h, hj, sub_self, zero_mul, add_zero]
        · rw [mul_zero, add_zero]
      have hcross : ∀ i, thdmK0 eta d u i * (if i = j then s else 0) = 0 := by
        intro i
        split_ifs with h
        · rw [h, thdm_K0_zero eta d u j hj, zero_mul]
        · rw [mul_zero]
      have ht : ∑ i, (if i = j then s else 0) * (if i = j then s else 0) = s * s := by
        rw [Finset.sum_congr rfl (fun i _ => show (if i = j then s else 0) *
          (if i = j then s else 0) = if i = j then s * s else 0 by split_ifs <;> ring)]
        simp
      have hss : s * s = thdmPsi eta d u := Real.mul_self_sqrt hPV
      have h0 := thdm_K0_sq eta d u
      have hkk : dot3 k k = 1 := by
        have : dot3 k k = dot3 (thdmK0 eta d u) (thdmK0 eta d u) +
            ∑ i, (if i = j then s else 0) * (if i = j then s else 0) := by
          simp only [dot3, hkdef, Fin.sum_univ_three]
          linear_combination 2 * hcross 0 + 2 * hcross 1 + 2 * hcross 2
        rw [this, ht, h0, hss]
        ring
      refine ⟨k, Or.inr ⟨hkk, u, (thdm_lin d eta u k).2 hk⟩, ?_⟩
      rw [thdm_fVal_diag eta00 eta d u hc, thdm_J4_diag_eq eta00 eta d k u hk, hkk]
      ring

lemma thdm_exists_diag (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ),
      Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ E = U * diagonal d * Uᵀ := by
  have hH : E.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hE
  have h1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have h2 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  simp only [Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    at h1 h2
  refine ⟨(hH.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℝ), hH.eigenvalues, h1, h2, ?_⟩
  conv_lhs => rw [hH.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, Function.id_comp]

open THDM in
lemma thdm_dot_mulVec (A : Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ) :
    dot3 x (A *ᵥ y) = dot3 (Aᵀ *ᵥ x) y := by
  show x ⬝ᵥ (A *ᵥ y) = (Aᵀ *ᵥ x) ⬝ᵥ y
  rw [dotProduct_mulVec, mulVec_transpose]

open THDM in
lemma thdm_dot_orth (U : Matrix (Fin 3) (Fin 3) ℝ) (hUU' : U * Uᵀ = 1) (x y : Fin 3 → ℝ) :
    dot3 x y = dot3 (Uᵀ *ᵥ x) (Uᵀ *ᵥ y) := by
  rw [thdm_dot_mulVec, transpose_transpose, mulVec_mulVec, hUU', one_mulVec]

lemma thdm_conj_apply (U A : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    (U * A * Uᵀ) *ᵥ x = U *ᵥ (A *ᵥ (Uᵀ *ᵥ x)) := by
  simp only [mulVec_mulVec, Matrix.mul_assoc]

lemma thdm_conj_mulVec (U A : Matrix (Fin 3) (Fin 3) ℝ) (hUU : Uᵀ * U = 1) (hUU' : U * Uᵀ = 1)
    (k y : Fin 3 → ℝ) :
    (U * A * Uᵀ) *ᵥ k = y ↔ A *ᵥ (Uᵀ *ᵥ k) = Uᵀ *ᵥ y := by
  rw [thdm_conj_apply]
  constructor
  · rintro rfl
    rw [mulVec_mulVec _ Uᵀ U, hUU, one_mulVec]
  · intro h
    rw [h, mulVec_mulVec, hUU', one_mulVec]

lemma thdm_sub_conj (U A : Matrix (Fin 3) (Fin 3) ℝ) (hUU' : U * Uᵀ = 1) (u : ℝ) :
    U * A * Uᵀ - u • (1 : Matrix (Fin 3) (Fin 3) ℝ) = U * (A - u • 1) * Uᵀ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU']

lemma thdm_det_conj (U A : Matrix (Fin 3) (Fin 3) ℝ) (hUU' : U * Uᵀ = 1) :
    (U * A * Uᵀ).det = A.det := by
  have h : U.det * U.det = 1 := by
    have := congrArg Matrix.det hUU'
    rwa [det_mul, det_transpose, det_one] at this
  rw [det_mul, det_mul, det_transpose]
  calc U.det * A.det * U.det = A.det * (U.det * U.det) := by ring
    _ = A.det := by rw [h, mul_one]

lemma thdm_inv_conj (U A : Matrix (Fin 3) (Fin 3) ℝ) (hUU : Uᵀ * U = 1) (hUU' : U * Uᵀ = 1) :
    (U * A * Uᵀ)⁻¹ = U * A⁻¹ * Uᵀ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hUU,
    Matrix.inv_eq_left_inv hUU', Matrix.mul_assoc]

open THDM in
lemma thdm_Reg_conj (U : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ) (hUU' : U * Uᵀ = 1) :
    Reg (U * diagonal d * Uᵀ) = Reg (diagonal d) := by
  funext u
  rw [Reg, Reg, thdm_sub_conj U _ hUU', thdm_det_conj U _ hUU']

open THDM in
lemma thdm_resolv_conj (U : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ)
    (hUU : Uᵀ * U = 1) (hUU' : U * Uᵀ = 1) (u : ℝ) :
    resolv (U * diagonal d * Uᵀ) u = U * resolv (diagonal d) u * Uᵀ := by
  rw [resolv, resolv, thdm_sub_conj U _ hUU', thdm_inv_conj U _ hUU hUU']

open THDM in
lemma thdm_fFun_conj (U : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ)
    (hUU : Uᵀ * U = 1) (hUU' : U * Uᵀ = 1) (eta00 : ℝ) (eta : Fin 3 → ℝ) :
    fFun eta00 eta (U * diagonal d * Uᵀ) = fFun eta00 (Uᵀ *ᵥ eta) (diagonal d) := by
  funext u
  rw [fFun, fFun, thdm_resolv_conj U d hUU hUU', thdm_conj_apply, thdm_dot_mulVec]

open THDM in
lemma thdm_fPrime_conj (U : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ)
    (hUU : Uᵀ * U = 1) (hUU' : U * Uᵀ = 1) (eta : Fin 3 → ℝ) :
    fPrime eta (U * diagonal d * Uᵀ) = fPrime (Uᵀ *ᵥ eta) (diagonal d) := by
  funext u
  have hm : ∀ A B : Matrix (Fin 3) (Fin 3) ℝ, (U * A * Uᵀ) * (U * B * Uᵀ) = U * (A * B) * Uᵀ := by
    intro A B
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U, hUU, Matrix.one_mul]
  rw [fPrime, fPrime, thdm_resolv_conj U d hUU hUU', hm, thdm_conj_apply, thdm_dot_mulVec]

open THDM in
lemma thdm_gFun_conj (U : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ)
    (hUU : Uᵀ * U = 1) (hUU' : U * Uᵀ = 1) (xi0 : ℝ) (xi eta : Fin 3 → ℝ) :
    gFun xi0 xi eta (U * diagonal d * Uᵀ) = gFun xi0 (Uᵀ *ᵥ xi) (Uᵀ *ᵥ eta) (diagonal d) := by
  funext u
  rw [gFun, gFun, thdm_resolv_conj U d hUU hUU', thdm_conj_apply, thdm_dot_mulVec]

open THDM in
lemma thdm_fVal_conj (U : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ)
    (hUU : Uᵀ * U = 1) (hUU' : U * Uᵀ = 1) (eta00 : ℝ) (eta : Fin 3 → ℝ) :
    fVal eta00 eta (U * diagonal d * Uᵀ) = fVal eta00 (Uᵀ *ᵥ eta) (diagonal d) := by
  funext u
  unfold fVal
  rw [thdm_Reg_conj U d hUU', thdm_fFun_conj U d hUU hUU']

open THDM in
lemma thdm_fPrimeVal_conj (U : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ)
    (hUU : Uᵀ * U = 1) (hUU' : U * Uᵀ = 1) (eta : Fin 3 → ℝ) :
    fPrimeVal eta (U * diagonal d * Uᵀ) = fPrimeVal (Uᵀ *ᵥ eta) (diagonal d) := by
  funext u
  unfold fPrimeVal
  rw [thdm_Reg_conj U d hUU', thdm_fPrime_conj U d hUU hUU']

open THDM in
lemma thdm_gVal_conj (U : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ)
    (hUU : Uᵀ * U = 1) (hUU' : U * Uᵀ = 1) (xi0 : ℝ) (xi eta : Fin 3 → ℝ) :
    gVal xi0 xi eta (U * diagonal d * Uᵀ) = gVal xi0 (Uᵀ *ᵥ xi) (Uᵀ *ᵥ eta) (diagonal d) := by
  funext u
  unfold gVal
  rw [thdm_Reg_conj U d hUU', thdm_gFun_conj U d hUU hUU']

open THDM in
lemma thdm_Iset_conj (U : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ)
    (hUU : Uᵀ * U = 1) (hUU' : U * Uᵀ = 1) (eta00 : ℝ) (eta : Fin 3 → ℝ) :
    Iset eta00 eta (U * diagonal d * Uᵀ) = Iset eta00 (Uᵀ *ᵥ eta) (diagonal d) := by
  unfold Iset
  rw [thdm_Reg_conj U d hUU', thdm_fFun_conj U d hUU hUU', thdm_fPrime_conj U d hUU hUU',
    thdm_fPrimeVal_conj U d hUU hUU']

open THDM in
lemma thdm_J4_conj (U : Matrix (Fin 3) (Fin 3) ℝ) (d : Fin 3 → ℝ) (hUU' : U * Uᵀ = 1)
    (eta00 : ℝ) (eta k : Fin 3 → ℝ) :
    J4 eta00 eta (U * diagonal d * Uᵀ) k = J4 eta00 (Uᵀ *ᵥ eta) (diagonal d) (Uᵀ *ᵥ k) := by
  rw [J4, J4, thdm_quad3_dot, thdm_quad3_dot, thdm_conj_apply, thdm_dot_mulVec,
    thdm_dot_orth U hUU' eta k]

open THDM in
lemma thdm_J2_conj (U : Matrix (Fin 3) (Fin 3) ℝ) (hUU' : U * Uᵀ = 1)
    (xi0 : ℝ) (xi k : Fin 3 → ℝ) :
    J2 xi0 xi k = J2 xi0 (Uᵀ *ᵥ xi) (Uᵀ *ᵥ k) := by
  rw [J2, J2, thdm_dot_orth U hUU' xi k]

open THDM Matrix in
theorem solution (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm) :
    {v : ℝ | ∃ k : Fin 3 → ℝ,
        ((dot3 k k < 1 ∧ E *ᵥ k = -eta) ∨
         (dot3 k k = 1 ∧ ∃ u : ℝ, (E - u • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ k = -eta)) ∧
        v = J4 eta00 eta E k}
      = (fun u => fVal eta00 eta E u) '' (Iset eta00 eta E) := by
  obtain ⟨U, d, hUU, hUU', rfl⟩ := thdm_exists_diag E hE
  rw [thdm_fVal_conj U d hUU hUU', thdm_Iset_conj U d hUU hUU', ← thdm_J4_diag eta00 (Uᵀ *ᵥ eta) d]
  ext v
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨Uᵀ *ᵥ k, ?_, thdm_J4_conj U d hUU' eta00 eta k⟩
    rw [← thdm_dot_orth U hUU' k k, ← mulVec_neg]
    rcases hk with ⟨h1, h2⟩ | ⟨h1, u, h2⟩
    · exact Or.inl ⟨h1, (thdm_conj_mulVec U _ hUU hUU' k _).1 h2⟩
    · rw [thdm_sub_conj U _ hUU'] at h2
      exact Or.inr ⟨h1, u, (thdm_conj_mulVec U _ hUU hUU' k _).1 h2⟩
  · rintro ⟨k', hk', rfl⟩
    have hk'' : Uᵀ *ᵥ (U *ᵥ k') = k' := by rw [mulVec_mulVec, hUU, one_mulVec]
    refine ⟨U *ᵥ k', ?_, by rw [thdm_J4_conj U d hUU' eta00 eta, hk'']⟩
    rw [thdm_dot_orth U hUU' (U *ᵥ k') (U *ᵥ k'), hk'']
    rcases hk' with ⟨h1, h2⟩ | ⟨h1, u, h2⟩
    · refine Or.inl ⟨h1, (thdm_conj_mulVec U _ hUU hUU' _ _).2 ?_⟩
      rw [hk'', mulVec_neg]
      exact h2
    · refine Or.inr ⟨h1, u, ?_⟩
      rw [thdm_sub_conj U _ hUU']
      apply (thdm_conj_mulVec U _ hUU hUU' _ _).2
      rw [hk'', mulVec_neg]
      exact h2

