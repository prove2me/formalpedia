-- Prove2me | solution 1 for THDM.thm1_stability_general_THDM
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T16:42:19.209366+00:00
-- url     : https://prove2.me/submissions/296f8fab-ca72-4684-b35c-381702504c8d

import Mathlib
import Definitions.Def_THDM_stationary

/-! 361a5d8b THDM.thm1_stability_general_THDM (Maniatis-von Manteuffel-Nachtmann-Nagel,
hep-ph/0605184, Theorem 1: stability criterion for the general two-Higgs-doublet potential).

Route.
* Spectral theorem (Mathlib `Matrix.IsHermitian.spectral_theorem`) gives an orthogonal `Q` and
  eigenvalues `lam` with `E = Q diag(lam) Qᵀ`; all of `f`, `f'`, `g` become explicit sums in the
  eigen-coordinates `Qᵀ η`, `Qᵀ ξ` (Lean's `x / 0 = 0` makes the formulas uniform).
* At an eigenvalue `u` the punctured limits exist iff `η` has no `u`-eigencomponent, and then
  `fVal`, `fPrimeVal`, `gVal` equal the explicit sums (termwise continuity + uniqueness of limits).
* `J₄` attains its minimum on the compact ball; an elementary first-order argument (variational
  inequality on the convex ball + equality in Cauchy-Schwarz) gives `(E - u) k = -η` with
  `|k| = 1` or `u = 0`, which places `u` in `Iset` with `fVal u = J₄ k` (bridge forward).
* Conversely each `u ∈ Iset` yields a point of the ball with `J₄ = fVal u` and, where required,
  `J₂ = g(u)` resp. `g(u) - |ξ⊥| √f'(u)` (bridge backward); unboundedness then follows from
  `V = K₀ J₂ + K₀² J₄`. The `V₄ ≡ 0` case is Cauchy-Schwarz. -/

set_option autoImplicit false
open scoped BigOperators
open Matrix

namespace THDMLib

open THDM

theorem spec3 (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm) :
    ∃ Q : Matrix (Fin 3) (Fin 3) ℝ, ∃ lam : Fin 3 → ℝ,
      Qᵀ * Q = 1 ∧ Q * Qᵀ = 1 ∧ E = Q * diagonal lam * Qᵀ := by
  have hH : E.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hE
  refine ⟨(hH.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℝ), hH.eigenvalues, ?_, ?_, ?_⟩
  · have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  · have := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa [Matrix.star_eq_conjTranspose] using this
  · have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [Matrix.star_eq_conjTranspose] using this

theorem dot3_eq_dotProduct (x y : Fin 3 → ℝ) : dot3 x y = x ⬝ᵥ y := rfl

theorem dot3_hat (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ2 : Q * Qᵀ = 1) (x y : Fin 3 → ℝ) :
    dot3 x y = ∑ i, (Qᵀ *ᵥ x) i * (Qᵀ *ᵥ y) i := by
  have h : ∑ i, (Qᵀ *ᵥ x) i * (Qᵀ *ᵥ y) i = (Qᵀ *ᵥ x) ⬝ᵥ (Qᵀ *ᵥ y) := rfl
  rw [h, mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, hQ2, one_mulVec]
  rfl

theorem hat_Q (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ1 : Qᵀ * Q = 1) (c : Fin 3 → ℝ) :
    Qᵀ *ᵥ (Q *ᵥ c) = c := by
  rw [mulVec_mulVec, hQ1, one_mulVec]

theorem Q_hat (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ2 : Q * Qᵀ = 1) (x : Fin 3 → ℝ) :
    Q *ᵥ (Qᵀ *ᵥ x) = x := by
  rw [mulVec_mulVec, hQ2, one_mulVec]

theorem hat_E (E Q : Matrix (Fin 3) (Fin 3) ℝ) (lam : Fin 3 → ℝ) (hQ1 : Qᵀ * Q = 1)
    (hEQ : E = Q * diagonal lam * Qᵀ) (x : Fin 3 → ℝ) (i : Fin 3) :
    (Qᵀ *ᵥ (E *ᵥ x)) i = lam i * (Qᵀ *ᵥ x) i := by
  rw [hEQ, ← mulVec_mulVec, ← mulVec_mulVec, hat_Q Q hQ1, mulVec_diagonal]

theorem hat_sub (E Q : Matrix (Fin 3) (Fin 3) ℝ) (lam : Fin 3 → ℝ) (hQ1 : Qᵀ * Q = 1)
    (hEQ : E = Q * diagonal lam * Qᵀ) (v : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) :
    (Qᵀ *ᵥ ((E - v • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ x)) i = (lam i - v) * (Qᵀ *ᵥ x) i := by
  rw [sub_mulVec, mulVec_sub, Pi.sub_apply, hat_E E Q lam hQ1 hEQ, smul_mulVec, one_mulVec,
    mulVec_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem quad3_eq (E : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    quad3 E x x = dot3 x (E *ᵥ x) := by
  unfold quad3 dot3
  simp only [mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem reg_iff (E Q : Matrix (Fin 3) (Fin 3) ℝ) (lam : Fin 3 → ℝ)
    (hQ2 : Q * Qᵀ = 1) (hEQ : E = Q * diagonal lam * Qᵀ) (v : ℝ) :
    Reg E v ↔ ∀ i, lam i ≠ v := by
  have hdecomp : E - v • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      = Q * diagonal (fun i => lam i - v) * Qᵀ := by
    have : diagonal (fun i => lam i - v) = diagonal lam - v • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, hEQ, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hQ2]
  have hdet : (E - v • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = ∏ i, (lam i - v) := by
    rw [hdecomp, det_mul, det_mul, det_diagonal]
    have h1 : Q.det * Qᵀ.det = 1 := by rw [← det_mul, hQ2, det_one]
    calc Q.det * (∏ i, (lam i - v)) * Qᵀ.det = (Q.det * Qᵀ.det) * ∏ i, (lam i - v) := by ring
      _ = ∏ i, (lam i - v) := by rw [h1, one_mul]
  unfold Reg
  rw [hdet, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  simp [sub_ne_zero]

theorem hat_resolv (E Q : Matrix (Fin 3) (Fin 3) ℝ) (lam : Fin 3 → ℝ) (hQ1 : Qᵀ * Q = 1)
    (hQ2 : Q * Qᵀ = 1) (hEQ : E = Q * diagonal lam * Qᵀ) (v : ℝ) (hv : Reg E v)
    (y : Fin 3 → ℝ) (i : Fin 3) :
    (Qᵀ *ᵥ (resolv E v *ᵥ y)) i = (Qᵀ *ᵥ y) i / (lam i - v) := by
  have hne : lam i - v ≠ 0 := sub_ne_zero.mpr ((reg_iff E Q lam hQ2 hEQ v).mp hv i)
  have hz : (E - v • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ (resolv E v *ᵥ y) = y := by
    unfold resolv
    rw [mulVec_mulVec, mul_nonsing_inv _ hv, one_mulVec]
  have := hat_sub E Q lam hQ1 hEQ v (resolv E v *ᵥ y) i
  rw [hz] at this
  rw [eq_div_iff hne, this, mul_comm]

theorem fFun_eq (eta00 : ℝ) (eta : Fin 3 → ℝ) (E Q : Matrix (Fin 3) (Fin 3) ℝ)
    (lam : Fin 3 → ℝ) (hQ1 : Qᵀ * Q = 1) (hQ2 : Q * Qᵀ = 1) (hEQ : E = Q * diagonal lam * Qᵀ)
    (v : ℝ) (hv : Reg E v) :
    fFun eta00 eta E v =
      v + eta00 - ∑ i, (Qᵀ *ᵥ eta) i * ((Qᵀ *ᵥ eta) i / (lam i - v)) := by
  unfold fFun
  rw [dot3_hat Q hQ2]
  simp only [hat_resolv E Q lam hQ1 hQ2 hEQ v hv]

theorem fPrime_eq (eta : Fin 3 → ℝ) (E Q : Matrix (Fin 3) (Fin 3) ℝ)
    (lam : Fin 3 → ℝ) (hQ1 : Qᵀ * Q = 1) (hQ2 : Q * Qᵀ = 1) (hEQ : E = Q * diagonal lam * Qᵀ)
    (v : ℝ) (hv : Reg E v) :
    fPrime eta E v =
      1 - ∑ i, (Qᵀ *ᵥ eta) i * ((Qᵀ *ᵥ eta) i / (lam i - v) / (lam i - v)) := by
  unfold fPrime
  rw [dot3_hat Q hQ2, ← mulVec_mulVec]
  simp only [hat_resolv E Q lam hQ1 hQ2 hEQ v hv]

theorem gFun_eq (xi0 : ℝ) (xi eta : Fin 3 → ℝ) (E Q : Matrix (Fin 3) (Fin 3) ℝ)
    (lam : Fin 3 → ℝ) (hQ1 : Qᵀ * Q = 1) (hQ2 : Q * Qᵀ = 1) (hEQ : E = Q * diagonal lam * Qᵀ)
    (v : ℝ) (hv : Reg E v) :
    gFun xi0 xi eta E v =
      xi0 - ∑ i, (Qᵀ *ᵥ xi) i * ((Qᵀ *ᵥ eta) i / (lam i - v)) := by
  unfold gFun
  rw [dot3_hat Q hQ2]
  simp only [hat_resolv E Q lam hQ1 hQ2 hEQ v hv]

theorem punctLim_eq (F : ℝ → ℝ) (u L : ℝ)
    (h : Filter.Tendsto F (nhdsWithin u {u}ᶜ) (nhds L)) : punctLim F u = L := by
  have hex : ∃ L, Filter.Tendsto F (nhdsWithin u {u}ᶜ) (nhds L) := ⟨L, h⟩
  unfold punctLim
  rw [dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec h

theorem ev_reg (E Q : Matrix (Fin 3) (Fin 3) ℝ) (lam : Fin 3 → ℝ)
    (hQ2 : Q * Qᵀ = 1) (hEQ : E = Q * diagonal lam * Qᵀ) (u : ℝ) :
    ∀ᶠ v in nhdsWithin u {u}ᶜ, Reg E v := by
  have h : ∀ i, ∀ᶠ v in nhdsWithin u {u}ᶜ, lam i ≠ v := by
    intro i
    by_cases hi : lam i = u
    · rw [hi]
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact fun h' => hv h'.symm
    · exact nhdsWithin_le_nhds ((eventually_ne_nhds (Ne.symm hi)).mono fun v hv => Ne.symm hv)
  filter_upwards [Filter.eventually_all.mpr h] with v hv
  exact (reg_iff E Q lam hQ2 hEQ v).mpr hv

theorem term_tendsto (a b l u : ℝ) (h : l = u → b = 0) :
    Filter.Tendsto (fun v => a * (b / (l - v))) (nhds u) (nhds (a * (b / (l - u)))) := by
  by_cases hb : b = 0
  · simp [hb]
  · have hne : l - u ≠ 0 := sub_ne_zero.mpr fun h' => hb (h h')
    exact tendsto_const_nhds.mul (tendsto_const_nhds.div
      (tendsto_const_nhds.sub Filter.tendsto_id) hne)

theorem term_tendsto2 (a b l u : ℝ) (h : l = u → b = 0) :
    Filter.Tendsto (fun v => a * (b / (l - v) / (l - v))) (nhds u)
      (nhds (a * (b / (l - u) / (l - u)))) := by
  by_cases hb : b = 0
  · simp [hb]
  · have hne : l - u ≠ 0 := sub_ne_zero.mpr fun h' => hb (h h')
    exact tendsto_const_nhds.mul ((tendsto_const_nhds.div
      (tendsto_const_nhds.sub Filter.tendsto_id) hne).div
      (tendsto_const_nhds.sub Filter.tendsto_id) hne)

/-- Under the admissibility condition `Adm u` the three stability functions have the explicit
eigen-coordinate values at `u`, and `f`, `f'` have limits at `u`. -/
theorem vals_of_adm (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E Q : Matrix (Fin 3) (Fin 3) ℝ) (lam : Fin 3 → ℝ) (hQ1 : Qᵀ * Q = 1) (hQ2 : Q * Qᵀ = 1)
    (hEQ : E = Q * diagonal lam * Qᵀ) (u : ℝ)
    (hadm : ∀ i, lam i = u → (Qᵀ *ᵥ eta) i = 0) :
    (∃ L : ℝ, Filter.Tendsto (fFun eta00 eta E) (nhdsWithin u {u}ᶜ) (nhds L)) ∧
    (∃ L : ℝ, Filter.Tendsto (fPrime eta E) (nhdsWithin u {u}ᶜ) (nhds L)) ∧
    fVal eta00 eta E u =
      u + eta00 - ∑ i, (Qᵀ *ᵥ eta) i * ((Qᵀ *ᵥ eta) i / (lam i - u)) ∧
    fPrimeVal eta E u =
      1 - ∑ i, (Qᵀ *ᵥ eta) i * ((Qᵀ *ᵥ eta) i / (lam i - u) / (lam i - u)) ∧
    gVal xi0 xi eta E u =
      xi0 - ∑ i, (Qᵀ *ᵥ xi) i * ((Qᵀ *ᵥ eta) i / (lam i - u)) := by
  have hF : Filter.Tendsto (fFun eta00 eta E) (nhdsWithin u {u}ᶜ)
      (nhds (u + eta00 - ∑ i, (Qᵀ *ᵥ eta) i * ((Qᵀ *ᵥ eta) i / (lam i - u)))) := by
    have h0 : Filter.Tendsto
        (fun v => v + eta00 - ∑ i, (Qᵀ *ᵥ eta) i * ((Qᵀ *ᵥ eta) i / (lam i - v))) (nhds u)
        (nhds (u + eta00 - ∑ i, (Qᵀ *ᵥ eta) i * ((Qᵀ *ᵥ eta) i / (lam i - u)))) :=
      (Filter.tendsto_id.add tendsto_const_nhds).sub
        (tendsto_finsetSum _ fun i _ => term_tendsto _ _ _ _ (hadm i))
    refine (h0.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [ev_reg E Q lam hQ2 hEQ u] with v hv
    exact (fFun_eq eta00 eta E Q lam hQ1 hQ2 hEQ v hv).symm
  have hP : Filter.Tendsto (fPrime eta E) (nhdsWithin u {u}ᶜ)
      (nhds (1 - ∑ i, (Qᵀ *ᵥ eta) i * ((Qᵀ *ᵥ eta) i / (lam i - u) / (lam i - u)))) := by
    have h0 : Filter.Tendsto
        (fun v => 1 - ∑ i, (Qᵀ *ᵥ eta) i * ((Qᵀ *ᵥ eta) i / (lam i - v) / (lam i - v)))
        (nhds u)
        (nhds (1 - ∑ i, (Qᵀ *ᵥ eta) i * ((Qᵀ *ᵥ eta) i / (lam i - u) / (lam i - u)))) :=
      tendsto_const_nhds.sub
        (tendsto_finsetSum _ fun i _ => term_tendsto2 _ _ _ _ (hadm i))
    refine (h0.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [ev_reg E Q lam hQ2 hEQ u] with v hv
    exact (fPrime_eq eta E Q lam hQ1 hQ2 hEQ v hv).symm
  have hG : Filter.Tendsto (gFun xi0 xi eta E) (nhdsWithin u {u}ᶜ)
      (nhds (xi0 - ∑ i, (Qᵀ *ᵥ xi) i * ((Qᵀ *ᵥ eta) i / (lam i - u)))) := by
    have h0 : Filter.Tendsto
        (fun v => xi0 - ∑ i, (Qᵀ *ᵥ xi) i * ((Qᵀ *ᵥ eta) i / (lam i - v))) (nhds u)
        (nhds (xi0 - ∑ i, (Qᵀ *ᵥ xi) i * ((Qᵀ *ᵥ eta) i / (lam i - u)))) :=
      tendsto_const_nhds.sub
        (tendsto_finsetSum _ fun i _ => term_tendsto _ _ _ _ (hadm i))
    refine (h0.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [ev_reg E Q lam hQ2 hEQ u] with v hv
    exact (gFun_eq xi0 xi eta E Q lam hQ1 hQ2 hEQ v hv).symm
  refine ⟨⟨_, hF⟩, ⟨_, hP⟩, ?_, ?_, ?_⟩
  · unfold fVal
    split_ifs with hr
    · exact fFun_eq eta00 eta E Q lam hQ1 hQ2 hEQ u hr
    · exact punctLim_eq _ _ _ hF
  · unfold fPrimeVal
    split_ifs with hr
    · exact fPrime_eq eta E Q lam hQ1 hQ2 hEQ u hr
    · exact punctLim_eq _ _ _ hP
  · unfold gVal
    split_ifs with hr
    · exact gFun_eq xi0 xi eta E Q lam hQ1 hQ2 hEQ u hr
    · exact punctLim_eq _ _ _ hG

/-- If `f` has a finite punctured limit at `u`, then `η` has no component in the
`u`-eigenspace. -/
theorem adm_of_tendsto (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E Q : Matrix (Fin 3) (Fin 3) ℝ) (lam : Fin 3 → ℝ) (hQ1 : Qᵀ * Q = 1) (hQ2 : Q * Qᵀ = 1)
    (hEQ : E = Q * diagonal lam * Qᵀ) (u : ℝ)
    (hL : ∃ L : ℝ, Filter.Tendsto (fFun eta00 eta E) (nhdsWithin u {u}ᶜ) (nhds L)) :
    ∀ i, lam i = u → (Qᵀ *ᵥ eta) i = 0 := by
  obtain ⟨L, hL⟩ := hL
  set e := Qᵀ *ᵥ eta with he
  have h1 : Filter.Tendsto (fun v => (v - u) * fFun eta00 eta E v) (nhdsWithin u {u}ᶜ)
      (nhds ((u - u) * L)) :=
    ((Filter.tendsto_id.sub tendsto_const_nhds).mono_left nhdsWithin_le_nhds).mul hL
  have hc : ∀ i, Filter.Tendsto
      (fun v => e i * (e i * (if lam i = u then -1 else (v - u) / (lam i - v)))) (nhds u)
      (nhds (e i * (e i * (if lam i = u then -1 else (u - u) / (lam i - u))))) := by
    intro i
    by_cases hi : lam i = u
    · simp only [hi, if_true]
      exact tendsto_const_nhds
    · simp only [hi, if_false]
      have hne : lam i - u ≠ 0 := sub_ne_zero.mpr hi
      exact tendsto_const_nhds.mul (tendsto_const_nhds.mul
        ((Filter.tendsto_id.sub tendsto_const_nhds).div
          (tendsto_const_nhds.sub Filter.tendsto_id) hne))
  have h2 : Filter.Tendsto
      (fun v => (v - u) * (v + eta00) -
        ∑ i, e i * (e i * (if lam i = u then -1 else (v - u) / (lam i - v))))
      (nhds u)
      (nhds ((u - u) * (u + eta00) -
        ∑ i, e i * (e i * (if lam i = u then -1 else (u - u) / (lam i - u))))) :=
    ((Filter.tendsto_id.sub tendsto_const_nhds).mul
      (Filter.tendsto_id.add tendsto_const_nhds)).sub
      (tendsto_finsetSum _ fun i _ => hc i)
  have h3 : Filter.Tendsto (fun v => (v - u) * fFun eta00 eta E v) (nhdsWithin u {u}ᶜ)
      (nhds ((u - u) * (u + eta00) -
        ∑ i, e i * (e i * (if lam i = u then -1 else (u - u) / (lam i - u))))) := by
    refine (h2.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [ev_reg E Q lam hQ2 hEQ u, self_mem_nhdsWithin] with v hv hvu
    have hvu' : v - u ≠ 0 := sub_ne_zero.mpr hvu
    rw [fFun_eq eta00 eta E Q lam hQ1 hQ2 hEQ v hv, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : lam i = u
    · simp only [hi, if_true]
      have : u - v ≠ 0 := fun h => hvu' (by linarith)
      field_simp
      ring
    · simp only [hi, if_false]
      ring
  have h4 := tendsto_nhds_unique h1 h3
  have h5 : ∑ i, (if lam i = u then e i * e i else 0) = 0 := by
    have : ∑ i, e i * (e i * (if lam i = u then -1 else (u - u) / (lam i - u)))
        = -∑ i, (if lam i = u then e i * e i else 0) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : lam i = u <;> simp [hi]
    rw [this] at h4
    simp only [sub_self, zero_mul] at h4
    linarith
  intro i hi
  have h6 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by
    by_cases hj : lam j = u
    · simp only [hj, if_true]; exact mul_self_nonneg _
    · simp only [hj, if_false]; exact le_refl _)).mp h5 i (Finset.mem_univ _)
  simp only [hi, if_true] at h6
  exact mul_self_eq_zero.mp h6

theorem dot3_self_nonneg (x : Fin 3 → ℝ) : 0 ≤ dot3 x x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

theorem dot3_self_eq_zero (x : Fin 3 → ℝ) (h : dot3 x x = 0) : x = 0 := by
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x j))).mp h i
    (Finset.mem_univ _)
  exact mul_self_eq_zero.mp this

theorem dot_E_symm (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm) (x y : Fin 3 → ℝ) :
    x ⬝ᵥ (E *ᵥ y) = y ⬝ᵥ (E *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hE.eq, dotProduct_comm]

theorem J4_line (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm)
    (k d : Fin 3 → ℝ) (t : ℝ) :
    J4 eta00 eta E (k + t • d) =
      J4 eta00 eta E k + 2 * t * dot3 (eta + E *ᵥ k) d + t ^ 2 * quad3 E d d := by
  unfold J4
  rw [quad3_eq, quad3_eq, quad3_eq]
  simp only [dot3_eq_dotProduct, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  have h1 := dot_E_symm E hE k d
  have h2 : (E *ᵥ k) ⬝ᵥ d = d ⬝ᵥ (E *ᵥ k) := dotProduct_comm _ _
  rw [h1, h2]
  ring

theorem ball_convex (a b : Fin 3 → ℝ) (ha : a ∈ ballK) (hb : b ∈ ballK) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : a + t • (b - a) ∈ ballK := by
  have hA : dot3 a a ≤ 1 := ha
  have hB : dot3 b b ≤ 1 := hb
  have hAB : 0 ≤ dot3 (a - b) (a - b) := dot3_self_nonneg _
  show dot3 (a + t • (b - a)) (a + t • (b - a)) ≤ 1
  simp only [dot3_eq_dotProduct, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, dotProduct_sub, sub_dotProduct] at hA hB hAB ⊢
  have hc : b ⬝ᵥ a = a ⬝ᵥ b := dotProduct_comm _ _
  rw [hc] at hAB ⊢
  have h1t : 0 ≤ 1 - t := by linarith
  nlinarith [mul_nonneg (mul_nonneg ht h1t) hAB, mul_nonneg h1t (sub_nonneg.mpr hA),
    mul_nonneg ht (sub_nonneg.mpr hB)]

theorem var_ineq (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm)
    (k : Fin 3 → ℝ) (hk : k ∈ ballK) (hmin : IsMinOn (J4 eta00 eta E) ballK k)
    (k' : Fin 3 → ℝ) (hk' : k' ∈ ballK) :
    0 ≤ dot3 (eta + E *ᵥ k) (k' - k) := by
  set a := dot3 (eta + E *ᵥ k) (k' - k) with ha
  set b := quad3 E (k' - k) (k' - k) with hb
  by_contra hneg0
  have hneg : a < 0 := lt_of_not_ge hneg0
  set t := min 1 (-a / (|b| + 1)) with ht
  have hb1 : 0 < |b| + 1 := by positivity
  have ht0 : 0 < t := lt_min one_pos (div_pos (neg_pos.mpr hneg) hb1)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t * (|b| + 1) ≤ -a := by
    have := min_le_right 1 (-a / (|b| + 1))
    rw [← ht, le_div_iff₀ hb1] at this
    exact this
  have hmem : k + t • (k' - k) ∈ ballK := ball_convex k k' hk hk' t ht0.le ht1
  have hle := isMinOn_iff.mp hmin _ hmem
  rw [J4_line eta00 eta E hE] at hle
  have h1 : t ^ 2 * b ≤ t ^ 2 * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) (sq_nonneg t)
  have h2 : t * (t * (|b| + 1)) ≤ t * (-a) := mul_le_mul_of_nonneg_left ht2 ht0.le
  have h3 : t * a < 0 := mul_neg_of_pos_of_neg ht0 hneg
  nlinarith [sq_nonneg t]

theorem lagrange (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm)
    (k : Fin 3 → ℝ) (hk : k ∈ ballK) (hmin : IsMinOn (J4 eta00 eta E) ballK k) :
    ∃ u : ℝ, (E - u • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ k = -eta ∧ (dot3 k k = 1 ∨ u = 0) := by
  set g := eta + E *ᵥ k with hg
  by_cases hg0 : g = 0
  · refine ⟨0, ?_, Or.inr rfl⟩
    rw [zero_smul, sub_zero]
    rw [hg] at hg0
    exact eq_neg_of_add_eq_zero_right hg0
  · have hgg : 0 < dot3 g g :=
      lt_of_le_of_ne (dot3_self_nonneg g) (fun h => hg0 (dot3_self_eq_zero g h.symm))
    set N := Real.sqrt (dot3 g g) with hN
    have hN0 : 0 < N := Real.sqrt_pos.mpr hgg
    have hNN : N * N = dot3 g g := Real.mul_self_sqrt hgg.le
    have hk'mem : (-(1 / N)) • g ∈ ballK := by
      show dot3 ((-(1 / N)) • g) ((-(1 / N)) • g) ≤ 1
      simp only [dot3_eq_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul] at hNN ⊢
      rw [← hNN]
      field_simp
      exact le_refl _
    have hv := var_ineq eta00 eta E hE k hk hmin _ hk'mem
    have hkk : dot3 k k ≤ 1 := hk
    simp only [dot3_eq_dotProduct, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hv hNN hkk
    -- hv : 0 ≤ -(1/N) * (g ⬝ᵥ g) - g ⬝ᵥ k
    have hgk : g ⬝ᵥ k ≤ -N := by
      rw [← hNN] at hv
      have : -(1 / N) * (N * N) = -N := by field_simp
      linarith
    have hsq : 0 ≤ (g + N • k) ⬝ᵥ (g + N • k) := dot3_self_nonneg _
    have hexp : (g + N • k) ⬝ᵥ (g + N • k) = g ⬝ᵥ g + 2 * N * (g ⬝ᵥ k) + N * N * (k ⬝ᵥ k) := by
      simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      rw [dotProduct_comm k g]
      ring
    have hNkk : N * N * (k ⬝ᵥ k) ≤ N * N := by
      have := mul_le_mul_of_nonneg_left hkk (mul_self_nonneg N)
      linarith
    have hzero : (g + N • k) ⬝ᵥ (g + N • k) = 0 := by
      apply le_antisymm _ hsq
      rw [hexp, ← hNN]
      nlinarith
    have hgNk : g + N • k = 0 := dot3_self_eq_zero _ hzero
    refine ⟨-N, ?_, Or.inl ?_⟩
    · rw [sub_mulVec, smul_mulVec, one_mulVec]
      have : E *ᵥ k = g - eta := by rw [hg]; abel
      rw [this]
      have h2 : g = -(N • k) := eq_neg_of_add_eq_zero_left hgNk
      rw [h2, neg_smul]
      abel
    · show k ⬝ᵥ k = 1
      rw [hexp, ← hNN] at hzero
      have hkk' : 1 ≤ k ⬝ᵥ k := by
        by_contra hlt0
        have hlt : k ⬝ᵥ k < 1 := lt_of_not_ge hlt0
        have : N * N * (k ⬝ᵥ k) < N * N := by
          have := mul_lt_mul_of_pos_left hlt (mul_pos hN0 hN0)
          linarith
        nlinarith
      linarith

theorem ballK_isCompact : IsCompact ballK := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have hc : Continuous fun k : Fin 3 → ℝ => dot3 k k := by
      unfold dot3
      fun_prop
    exact isClosed_le hc continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Fin 3 → ℝ)) (r := 1)).subset ?_
    intro k hk
    have hk' : dot3 k k ≤ 1 := hk
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
    have : k i * k i ≤ dot3 k k :=
      Finset.single_le_sum (f := fun j => k j * k j) (fun j _ => mul_self_nonneg (k j))
        (Finset.mem_univ i)
    nlinarith

theorem exists_min (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ k ∈ ballK, IsMinOn (J4 eta00 eta E) ballK k := by
  have hne : ballK.Nonempty := ⟨0, by show dot3 0 0 ≤ 1; simp [dot3]⟩
  have hc : Continuous (J4 eta00 eta E) := by
    unfold J4 dot3 quad3
    fun_prop
  exact ballK_isCompact.exists_isMinOn hne hc.continuousOn

theorem not_stable_of (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (k : Fin 3 → ℝ) (hk : k ∈ ballK)
    (h : J4 eta00 eta E k < 0 ∨ (J4 eta00 eta E k ≤ 0 ∧ J2 xi0 xi k < 0)) :
    ¬ Stable xi0 xi eta00 eta E := by
  rintro ⟨C, hC⟩
  set a := J4 eta00 eta E k with ha
  set b := J2 xi0 xi k with hb
  have hCabs : -|C| ≤ C := neg_abs_le C
  rcases h with h | ⟨h1, h2⟩
  · set t := max 1 ((|b| + |C| + 1) / (-a)) with ht
    have ht1 : 1 ≤ t := le_max_left _ _
    have hna : 0 < -a := neg_pos.mpr h
    have ht2 : |b| + |C| + 1 ≤ t * (-a) := by
      have := le_max_right 1 ((|b| + |C| + 1) / (-a))
      rw [← ht, div_le_iff₀ hna] at this
      exact this
    have hV := hC t k hk (by linarith)
    unfold Vpot at hV
    rw [← ha, ← hb] at hV
    have e1 : t * b ≤ t * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) (by linarith)
    have e2 : t * (|b| + |C| + 1) ≤ t * (t * (-a)) := mul_le_mul_of_nonneg_left ht2 (by linarith)
    have e3 : 0 ≤ (t - 1) * (|C| + 1) := mul_nonneg (by linarith) (by positivity)
    nlinarith
  · have hnb : 0 < -b := neg_pos.mpr h2
    set t := (|C| + 1) / (-b) with ht
    have ht0 : 0 ≤ t := div_nonneg (by positivity) hnb.le
    have hb0 : b ≠ 0 := h2.ne
    have htb : t * b = -(|C| + 1) := by
      rw [ht]; field_simp
    have hV := hC t k hk ht0
    unfold Vpot at hV
    rw [← ha, ← hb] at hV
    have : t ^ 2 * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) h1
    linarith

theorem hat_inj (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ2 : Q * Qᵀ = 1) (x y : Fin 3 → ℝ)
    (h : Qᵀ *ᵥ x = Qᵀ *ᵥ y) : x = y := by
  rw [← Q_hat Q hQ2 x, h, Q_hat Q hQ2 y]

theorem J4_of_stat (eta00 : ℝ) (eta : Fin 3 → ℝ) (E : Matrix (Fin 3) (Fin 3) ℝ) (u : ℝ)
    (k : Fin 3 → ℝ) (hk : (E - u • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ k = -eta) :
    J4 eta00 eta E k = eta00 + dot3 eta k + u * dot3 k k := by
  have hEk : E *ᵥ k = -eta + u • k := by
    rw [sub_mulVec, smul_mulVec, one_mulVec] at hk
    rw [← hk]; abel
  unfold J4
  rw [quad3_eq, hEk]
  simp only [dot3_eq_dotProduct, dotProduct_add, dotProduct_neg, dotProduct_smul, smul_eq_mul,
    dotProduct_comm k eta]
  ring

theorem eigproj_coords (E Q : Matrix (Fin 3) (Fin 3) ℝ) (lam : Fin 3 → ℝ) (hQ1 : Qᵀ * Q = 1)
    (hQ2 : Q * Qᵀ = 1) (hEQ : E = Q * diagonal lam * Qᵀ) (u : ℝ) (xi p : Fin 3 → ℝ)
    (hp : IsEigenProj E u xi p) (i : Fin 3) :
    (Qᵀ *ᵥ p) i = if lam i = u then (Qᵀ *ᵥ xi) i else 0 := by
  obtain ⟨hp1, hp2⟩ := hp
  by_cases hi : lam i = u
  · rw [if_pos hi]
    have hw : (E - u • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ (Q *ᵥ Pi.single i 1) = 0 := by
      apply hat_inj Q hQ2
      funext j
      rw [mulVec_zero, hat_sub E Q lam hQ1 hEQ u, hat_Q Q hQ1]
      by_cases hj : j = i
      · subst hj; rw [hi, sub_self, zero_mul]; rfl
      · rw [Pi.single_eq_of_ne hj, mul_zero]; rfl
    have h := hp2 _ hw
    rw [dot3_hat Q hQ2, mulVec_sub, hat_Q Q hQ1] at h
    simp only [Pi.sub_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    linarith
  · rw [if_neg hi]
    have h := hat_sub E Q lam hQ1 hEQ u p i
    rw [hp1, mulVec_zero] at h
    have hne : lam i - u ≠ 0 := sub_ne_zero.mpr hi
    have h0 : (lam i - u) * (Qᵀ *ᵥ p) i = 0 := by rw [← h]; rfl
    exact (mul_eq_zero.mp h0).resolve_left hne

theorem exists_m (E Q : Matrix (Fin 3) (Fin 3) ℝ) (lam : Fin 3 → ℝ) (hQ1 : Qᵀ * Q = 1)
    (hQ2 : Q * Qᵀ = 1) (hEQ : E = Q * diagonal lam * Qᵀ) (u : ℝ) (xi p : Fin 3 → ℝ)
    (hr : ¬ Reg E u) (hp : IsEigenProj E u xi p) :
    ∃ m : Fin 3 → ℝ, (∀ i, lam i ≠ u → m i = 0) ∧ ∑ i, m i * m i = 1 ∧
      ∑ i, (Qᵀ *ᵥ xi) i * m i = -norm3 p := by
  have hpc := eigproj_coords E Q lam hQ1 hQ2 hEQ u xi p hp
  by_cases hp0 : p = 0
  · have hj : ∃ j, lam j = u := by
      by_contra hno
      apply hr
      rw [reg_iff E Q lam hQ2 hEQ u]
      intro i hi
      exact hno ⟨i, hi⟩
    obtain ⟨j, hj⟩ := hj
    refine ⟨Pi.single j 1, ?_, ?_, ?_⟩
    · intro i hi
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      exact Pi.single_eq_of_ne hij _
    · simp [Pi.single_apply]
    · have h1 := hpc j
      rw [if_pos hj, hp0, mulVec_zero] at h1
      have hn : norm3 (0 : Fin 3 → ℝ) = 0 := by simp [norm3, dot3]
      rw [hp0, hn]
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      rw [← h1]; simp
  · have hpp : 0 < dot3 p p :=
      lt_of_le_of_ne (dot3_self_nonneg p) (fun h => hp0 (dot3_self_eq_zero p h.symm))
    have hN0 : 0 < norm3 p := Real.sqrt_pos.mpr hpp
    have hNN : norm3 p * norm3 p = ∑ i, (Qᵀ *ᵥ p) i * (Qᵀ *ᵥ p) i := by
      unfold norm3; rw [Real.mul_self_sqrt hpp.le, dot3_hat Q hQ2]
    have hxp : ∑ i, (Qᵀ *ᵥ xi) i * (Qᵀ *ᵥ p) i = ∑ i, (Qᵀ *ᵥ p) i * (Qᵀ *ᵥ p) i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hpc i]
      by_cases hi : lam i = u
      · rw [if_pos hi]
      · rw [if_neg hi, mul_zero, mul_zero]
    refine ⟨fun i => -(Qᵀ *ᵥ p) i / norm3 p, ?_, ?_, ?_⟩
    · intro i hi
      simp only
      rw [hpc i, if_neg hi, neg_zero, zero_div]
    · have : ∑ i, -(Qᵀ *ᵥ p) i / norm3 p * (-(Qᵀ *ᵥ p) i / norm3 p)
          = (∑ i, (Qᵀ *ᵥ p) i * (Qᵀ *ᵥ p) i) / (norm3 p * norm3 p) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        field_simp
      rw [this, ← hNN, div_self (mul_pos hN0 hN0).ne']
    · have : ∑ i, (Qᵀ *ᵥ xi) i * (-(Qᵀ *ᵥ p) i / norm3 p)
          = -(∑ i, (Qᵀ *ᵥ xi) i * (Qᵀ *ᵥ p) i) / norm3 p := by
        rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [this, hxp, ← hNN]
      field_simp

theorem bridge_fwd (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm) (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (lam : Fin 3 → ℝ) (hQ1 : Qᵀ * Q = 1) (hQ2 : Q * Qᵀ = 1) (hEQ : E = Q * diagonal lam * Qᵀ)
    (k : Fin 3 → ℝ) (hk : k ∈ ballK) (hmin : IsMinOn (J4 eta00 eta E) ballK k) :
    ∃ u ∈ Iset eta00 eta E, fVal eta00 eta E u = J4 eta00 eta E k ∧
      (Reg E u → gVal xi0 xi eta E u = J2 xi0 xi k) ∧
      (¬ Reg E u → ∃ p : Fin 3 → ℝ, IsEigenProj E u xi p ∧
        gVal xi0 xi eta E u - norm3 p * Real.sqrt (fPrimeVal eta E u) ≤ J2 xi0 xi k) := by
  obtain ⟨u, hku, hcase⟩ := lagrange eta00 eta E hE k hk hmin
  have hkk : dot3 k k ≤ 1 := hk
  have hcoord : ∀ i, (lam i - u) * (Qᵀ *ᵥ k) i = -(Qᵀ *ᵥ eta) i := by
    intro i
    rw [← hat_sub E Q lam hQ1 hEQ u k i, hku, mulVec_neg, Pi.neg_apply]
  have hadm : ∀ i, lam i = u → (Qᵀ *ᵥ eta) i = 0 := by
    intro i hi
    have := hcoord i
    rw [hi, sub_self, zero_mul] at this
    linarith
  obtain ⟨hL1, hL2, hf, hfp, hg⟩ := vals_of_adm xi0 xi eta00 eta E Q lam hQ1 hQ2 hEQ u hadm
  obtain ⟨c, hc⟩ : ∃ c : Fin 3 → ℝ, ∀ i, c i = if lam i = u then 0 else (Qᵀ *ᵥ k) i :=
    ⟨_, fun i => rfl⟩
  have hdiv : ∀ i, (Qᵀ *ᵥ eta) i / (lam i - u) = -c i := by
    intro i
    rw [hc i]
    by_cases hi : lam i = u
    · rw [if_pos hi, hadm i hi, zero_div, neg_zero]
    · have hne : lam i - u ≠ 0 := sub_ne_zero.mpr hi
      rw [if_neg hi, div_eq_iff hne]
      linarith [hcoord i]
  have hdiv2 : ∀ i, (Qᵀ *ᵥ eta) i * ((Qᵀ *ᵥ eta) i / (lam i - u) / (lam i - u)) = c i * c i := by
    intro i
    rw [hdiv i]
    by_cases hi : lam i = u
    · rw [hc i, if_pos hi, hadm i hi]; ring
    · have hne : lam i - u ≠ 0 := sub_ne_zero.mpr hi
      have he : (Qᵀ *ᵥ eta) i = -((lam i - u) * (Qᵀ *ᵥ k) i) := by linarith [hcoord i]
      rw [hc i, if_neg hi, he]
      field_simp
  have hec : ∀ i, (Qᵀ *ᵥ eta) i * c i = (Qᵀ *ᵥ eta) i * (Qᵀ *ᵥ k) i := by
    intro i
    rw [hc i]
    by_cases hi : lam i = u
    · rw [if_pos hi, hadm i hi, zero_mul, zero_mul]
    · rw [if_neg hi]
  have hJ4 := J4_of_stat eta00 eta E u k hku
  have huk : u * dot3 k k = u := by
    rcases hcase with h | h
    · rw [h, mul_one]
    · rw [h, zero_mul]
  have hfval : fVal eta00 eta E u = J4 eta00 eta E k := by
    rw [hf, hJ4, huk, dot3_hat Q hQ2 eta k]
    simp only [hdiv, mul_neg, Finset.sum_neg_distrib, hec]
    ring
  have hfpv : fPrimeVal eta E u = 1 - ∑ i, c i * c i := by
    rw [hfp]
    simp only [hdiv2]
  have hgv : gVal xi0 xi eta E u = xi0 + ∑ i, (Qᵀ *ᵥ xi) i * c i := by
    rw [hg]
    simp only [hdiv, mul_neg, Finset.sum_neg_distrib]
    ring
  refine ⟨u, ?_, hfval, ?_, ?_⟩
  · by_cases hr : Reg E u
    · have hlam := (reg_iff E Q lam hQ2 hEQ u).mp hr
      have hck : ∀ i, c i = (Qᵀ *ᵥ k) i := fun i => by rw [hc i, if_neg (hlam i)]
      have hfp' : fPrime eta E u = 1 - dot3 k k := by
        have : fPrimeVal eta E u = fPrime eta E u := by
          unfold fPrimeVal
          rw [if_pos hr]
        rw [← this, hfpv, dot3_hat Q hQ2 k k]
        simp only [hck]
      by_cases h1 : dot3 k k = 1
      · left; left
        exact ⟨hr, by rw [hfp', h1, sub_self]⟩
      · have h0 : u = 0 := hcase.resolve_left h1
        have hlt : dot3 k k < 1 := lt_of_le_of_ne hkk h1
        left; right
        refine ⟨h0, h0 ▸ hr, ?_⟩
        rw [← h0, hfp']
        linarith
    · right
      refine ⟨hr, hL1, hL2, ?_⟩
      have hsumc : ∑ i, c i * c i ≤ dot3 k k := by
        rw [dot3_hat Q hQ2 k k]
        apply Finset.sum_le_sum
        intro i _
        rw [hc i]
        by_cases hi : lam i = u
        · rw [if_pos hi, mul_zero]
          exact mul_self_nonneg _
        · rw [if_neg hi]
      rw [hfpv]
      linarith
  · intro hr
    have hlam := (reg_iff E Q lam hQ2 hEQ u).mp hr
    have hck : ∀ i, c i = (Qᵀ *ᵥ k) i := fun i => by rw [hc i, if_neg (hlam i)]
    rw [hgv]
    unfold J2
    rw [dot3_hat Q hQ2 xi k]
    simp only [hck]
  · intro hr
    obtain ⟨pc, hpc⟩ : ∃ pc : Fin 3 → ℝ, ∀ i, pc i = if lam i = u then (Qᵀ *ᵥ xi) i else 0 :=
      ⟨_, fun i => rfl⟩
    obtain ⟨d, hd⟩ : ∃ d : Fin 3 → ℝ, ∀ i, d i = if lam i = u then (Qᵀ *ᵥ k) i else 0 :=
      ⟨_, fun i => rfl⟩
    refine ⟨Q *ᵥ pc, ⟨?_, ?_⟩, ?_⟩
    · apply hat_inj Q hQ2
      funext i
      rw [mulVec_zero, hat_sub E Q lam hQ1 hEQ u, hat_Q Q hQ1, hpc i]
      by_cases hi : lam i = u
      · rw [hi, sub_self, zero_mul]; rfl
      · rw [if_neg hi, mul_zero]; rfl
    · intro w hw
      rw [dot3_hat Q hQ2, mulVec_sub, hat_Q Q hQ1]
      apply Finset.sum_eq_zero
      intro i _
      rw [Pi.sub_apply, hpc i]
      by_cases hi : lam i = u
      · rw [if_pos hi, sub_self, zero_mul]
      · have h := hat_sub E Q lam hQ1 hEQ u w i
        rw [hw, mulVec_zero] at h
        have hne : lam i - u ≠ 0 := sub_ne_zero.mpr hi
        have h0 : (lam i - u) * (Qᵀ *ᵥ w) i = 0 := by rw [← h]; rfl
        rw [(mul_eq_zero.mp h0).resolve_left hne, mul_zero]
    · have hJ2 : J2 xi0 xi k = gVal xi0 xi eta E u + ∑ i, pc i * d i := by
        rw [hgv]
        unfold J2
        rw [dot3_hat Q hQ2 xi k, add_assoc, ← Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [hc i, hpc i, hd i]
        by_cases hi : lam i = u
        · rw [if_pos hi, if_pos hi, if_pos hi]; ring
        · rw [if_neg hi, if_neg hi, if_neg hi]; ring
      have hnp : norm3 (Q *ᵥ pc) = Real.sqrt (∑ i, pc i ^ 2) := by
        unfold norm3
        rw [dot3_hat Q hQ2, hat_Q Q hQ1]
        simp only [sq]
      have hdd : ∑ i, (-d i) ^ 2 ≤ fPrimeVal eta E u := by
        rw [hfpv]
        have : ∑ i, (-d i) ^ 2 + ∑ i, c i * c i = dot3 k k := by
          rw [dot3_hat Q hQ2 k k, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [hc i, hd i]
          by_cases hi : lam i = u
          · rw [if_pos hi, if_pos hi]; ring
          · rw [if_neg hi, if_neg hi]; ring
        linarith
      have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ pc (fun i => -d i)
      have hsq : Real.sqrt (∑ i, (-d i) ^ 2) ≤ Real.sqrt (fPrimeVal eta E u) :=
        Real.sqrt_le_sqrt hdd
      have hnn : 0 ≤ Real.sqrt (∑ i, pc i ^ 2) := Real.sqrt_nonneg _
      have hneg : ∑ i, pc i * -d i = -∑ i, pc i * d i := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hJ2, hnp]
      rw [hneg] at hcs
      nlinarith [mul_le_mul_of_nonneg_left hsq hnn]

theorem bridge_bwd_reg (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (lam : Fin 3 → ℝ) (hQ1 : Qᵀ * Q = 1) (hQ2 : Q * Qᵀ = 1) (hEQ : E = Q * diagonal lam * Qᵀ)
    (u : ℝ) (hu : u ∈ Iset eta00 eta E) (hr : Reg E u) :
    ∃ k ∈ ballK, J4 eta00 eta E k = fVal eta00 eta E u ∧ J2 xi0 xi k = gVal xi0 xi eta E u := by
  have hfp0 : 0 ≤ fPrime eta E u ∧ u * fPrime eta E u = 0 := by
    rcases hu with (⟨_, h⟩ | ⟨h0, _, h⟩) | ⟨h, _⟩
    · exact ⟨h.ge, by rw [h, mul_zero]⟩
    · exact ⟨h0 ▸ h.le, by rw [h0, zero_mul]⟩
    · exact absurd hr h
  have hkk : dot3 (-(resolv E u *ᵥ eta)) (-(resolv E u *ᵥ eta)) = 1 - fPrime eta E u := by
    rw [fPrime_eq eta E Q lam hQ1 hQ2 hEQ u hr, dot3_hat Q hQ2, sub_sub_cancel]
    apply Finset.sum_congr rfl
    intro i _
    rw [mulVec_neg, Pi.neg_apply, hat_resolv E Q lam hQ1 hQ2 hEQ u hr]
    ring
  have hstat : (E - u • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ (-(resolv E u *ᵥ eta)) = -eta := by
    unfold resolv
    rw [mulVec_neg, mulVec_mulVec, mul_nonsing_inv _ hr, one_mulVec]
  refine ⟨-(resolv E u *ᵥ eta), ?_, ?_, ?_⟩
  · show dot3 _ _ ≤ 1
    rw [hkk]
    linarith [hfp0.1]
  · rw [J4_of_stat eta00 eta E u _ hstat, hkk]
    unfold fVal
    rw [if_pos hr]
    unfold fFun
    simp only [dot3_eq_dotProduct, dotProduct_neg]
    linarith [hfp0.2]
  · unfold J2 gVal
    rw [if_pos hr]
    unfold gFun
    simp only [dot3_eq_dotProduct, dotProduct_neg]
    ring

theorem bridge_bwd_irr (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (lam : Fin 3 → ℝ) (hQ1 : Qᵀ * Q = 1) (hQ2 : Q * Qᵀ = 1) (hEQ : E = Q * diagonal lam * Qᵀ)
    (u : ℝ) (hu : u ∈ Iset eta00 eta E) (hr : ¬ Reg E u) (p : Fin 3 → ℝ)
    (hp : IsEigenProj E u xi p) :
    ∃ k ∈ ballK, J4 eta00 eta E k = fVal eta00 eta E u ∧
      J2 xi0 xi k = gVal xi0 xi eta E u - norm3 p * Real.sqrt (fPrimeVal eta E u) := by
  obtain ⟨hL1, hfpn⟩ : (∃ L : ℝ, Filter.Tendsto (fFun eta00 eta E) (nhdsWithin u {u}ᶜ)
      (nhds L)) ∧ 0 ≤ fPrimeVal eta E u := by
    rcases hu with (⟨h, _⟩ | ⟨h0, h, _⟩) | ⟨_, h1, _, h3⟩
    · exact absurd h hr
    · exact absurd (h0 ▸ h) hr
    · exact ⟨h1, h3⟩
  have hadm := adm_of_tendsto eta00 eta E Q lam hQ1 hQ2 hEQ u hL1
  obtain ⟨_, _, hf, hfp, hg⟩ := vals_of_adm xi0 xi eta00 eta E Q lam hQ1 hQ2 hEQ u hadm
  obtain ⟨m, hm1, hm2, hm3⟩ := exists_m E Q lam hQ1 hQ2 hEQ u xi p hr hp
  set s := Real.sqrt (fPrimeVal eta E u) with hs
  have hss : s * s = fPrimeVal eta E u := Real.mul_self_sqrt hfpn
  obtain ⟨c, hc⟩ : ∃ c : Fin 3 → ℝ, ∀ i, c i = -((Qᵀ *ᵥ eta) i / (lam i - u)) :=
    ⟨_, fun i => rfl⟩
  have hcm : ∀ i, c i * m i = 0 := by
    intro i
    by_cases hi : lam i = u
    · rw [hc i, hadm i hi, zero_div, neg_zero, zero_mul]
    · rw [hm1 i hi, mul_zero]
  have hem : ∀ i, (Qᵀ *ᵥ eta) i * m i = 0 := by
    intro i
    by_cases hi : lam i = u
    · rw [hadm i hi, zero_mul]
    · rw [hm1 i hi, mul_zero]
  have hcc : ∀ i, (Qᵀ *ᵥ eta) i * ((Qᵀ *ᵥ eta) i / (lam i - u) / (lam i - u)) = c i * c i := by
    intro i
    rw [hc i]
    ring
  have hkh : Qᵀ *ᵥ (Q *ᵥ (fun i => c i + s * m i)) = fun i => c i + s * m i := hat_Q Q hQ1 _
  have hkk : dot3 (Q *ᵥ (fun i => c i + s * m i)) (Q *ᵥ (fun i => c i + s * m i)) = 1 := by
    rw [dot3_hat Q hQ2, hkh]
    have : ∀ i, (c i + s * m i) * (c i + s * m i)
        = c i * c i + s * s * (m i * m i) + 2 * s * (c i * m i) := fun i => by ring
    simp only [this, hcm, mul_zero, add_zero, Finset.sum_add_distrib, ← Finset.mul_sum, hm2,
      mul_one, hss, hfp]
    simp only [hcc]
    ring
  have hstat : (E - u • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ (Q *ᵥ (fun i => c i + s * m i))
      = -eta := by
    apply hat_inj Q hQ2
    funext i
    rw [hat_sub E Q lam hQ1 hEQ u, hkh, mulVec_neg, Pi.neg_apply]
    by_cases hi : lam i = u
    · rw [hi, sub_self, zero_mul, hadm i hi, neg_zero]
    · have hne : lam i - u ≠ 0 := sub_ne_zero.mpr hi
      show (lam i - u) * (c i + s * m i) = -(Qᵀ *ᵥ eta) i
      rw [hm1 i hi, mul_zero, add_zero, hc i]
      field_simp
  refine ⟨Q *ᵥ (fun i => c i + s * m i), ?_, ?_, ?_⟩
  · show dot3 _ _ ≤ 1
    rw [hkk]
  · rw [J4_of_stat eta00 eta E u _ hstat, hkk, hf, dot3_hat Q hQ2, hkh]
    have : ∀ i, (Qᵀ *ᵥ eta) i * (c i + s * m i)
        = -((Qᵀ *ᵥ eta) i * ((Qᵀ *ᵥ eta) i / (lam i - u))) + s * ((Qᵀ *ᵥ eta) i * m i) :=
      fun i => by rw [hc i]; ring
    simp only [this, hem, mul_zero, add_zero, Finset.sum_neg_distrib]
    ring
  · unfold J2
    rw [hg, dot3_hat Q hQ2, hkh]
    have : ∀ i, (Qᵀ *ᵥ xi) i * (c i + s * m i)
        = -((Qᵀ *ᵥ xi) i * ((Qᵀ *ᵥ eta) i / (lam i - u))) + s * ((Qᵀ *ᵥ xi) i * m i) :=
      fun i => by rw [hc i]; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, hm3]
    ring

theorem exists_eigenProj (E Q : Matrix (Fin 3) (Fin 3) ℝ) (lam : Fin 3 → ℝ)
    (hQ1 : Qᵀ * Q = 1) (hQ2 : Q * Qᵀ = 1) (hEQ : E = Q * diagonal lam * Qᵀ) (u : ℝ)
    (xi : Fin 3 → ℝ) : ∃ p : Fin 3 → ℝ, IsEigenProj E u xi p := by
  obtain ⟨pc, hpc⟩ : ∃ pc : Fin 3 → ℝ, ∀ i, pc i = if lam i = u then (Qᵀ *ᵥ xi) i else 0 :=
    ⟨_, fun i => rfl⟩
  refine ⟨Q *ᵥ pc, ?_, ?_⟩
  · apply hat_inj Q hQ2
    funext i
    rw [mulVec_zero, hat_sub E Q lam hQ1 hEQ u, hat_Q Q hQ1, hpc i]
    by_cases hi : lam i = u
    · rw [hi, sub_self, zero_mul]; rfl
    · rw [if_neg hi, mul_zero]; rfl
  · intro w hw
    rw [dot3_hat Q hQ2, mulVec_sub, hat_Q Q hQ1]
    apply Finset.sum_eq_zero
    intro i _
    rw [Pi.sub_apply, hpc i]
    by_cases hi : lam i = u
    · rw [if_pos hi, sub_self, zero_mul]
    · have h := hat_sub E Q lam hQ1 hEQ u w i
      rw [hw, mulVec_zero] at h
      have hne : lam i - u ≠ 0 := sub_ne_zero.mpr hi
      have h0 : (lam i - u) * (Qᵀ *ᵥ w) i = 0 := by rw [← h]; rfl
      rw [(mul_eq_zero.mp h0).resolve_left hne, mul_zero]

theorem cs_bound (xi k : Fin 3 → ℝ) (hk : k ∈ ballK) : -norm3 xi ≤ dot3 xi k := by
  have hkk : dot3 k k ≤ 1 := hk
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ xi (fun i => -k i)
  have h1 : ∑ i, xi i * -k i = -dot3 xi k := by
    unfold dot3
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : Real.sqrt (∑ i, (-k i) ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    have : ∑ i, (-k i) ^ 2 = dot3 k k := by
      unfold dot3
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [this]
    exact hkk
  have h3 : Real.sqrt (∑ i, xi i ^ 2) = norm3 xi := by
    unfold norm3 dot3
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h1, h3] at hcs
  have hn : 0 ≤ norm3 xi := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h2 hn]

theorem anti_unit (xi : Fin 3 → ℝ) :
    (-(1 / norm3 xi)) • xi ∈ ballK ∧ dot3 xi ((-(1 / norm3 xi)) • xi) = -norm3 xi := by
  have hNN : norm3 xi * norm3 xi = dot3 xi xi := Real.mul_self_sqrt (dot3_self_nonneg xi)
  simp only [dot3_eq_dotProduct] at hNN
  constructor
  · show dot3 _ _ ≤ 1
    simp only [dot3_eq_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [← hNN]
    by_cases h0 : norm3 xi = 0
    · rw [h0]; norm_num
    · field_simp
      exact le_refl _
  · simp only [dot3_eq_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← hNN]
    by_cases h0 : norm3 xi = 0
    · rw [h0]; norm_num
    · field_simp

theorem J4_trivial (k : Fin 3 → ℝ) : J4 0 0 0 k = 0 := by
  simp [J4, dot3, quad3]

theorem v4_part (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) :
    V4Trivial eta00 eta E →
        ((norm3 xi < xi0 → Stable xi0 xi eta00 eta E) ∧
         (xi0 = norm3 xi → MarginalCase xi0 xi eta00 eta E ∧ Stable xi0 xi eta00 eta E) ∧
         (xi0 < norm3 xi → ¬ Stable xi0 xi eta00 eta E)) := by
  rintro ⟨h00, heta, hE0⟩
  subst h00 heta hE0
  have hstab : 0 ≤ xi0 - norm3 xi → Stable xi0 xi 0 0 0 := by
    intro h
    refine ⟨0, fun k0 k hk hk0 => ?_⟩
    unfold Vpot
    rw [J4_trivial, mul_zero, add_zero]
    have := cs_bound xi k hk
    unfold J2
    exact mul_nonneg hk0 (by linarith)
  refine ⟨fun h => hstab (by linarith), fun h => ⟨⟨?_, ?_⟩, hstab (by linarith)⟩, fun h => ?_⟩
  · intro k hk
    right
    refine ⟨J4_trivial k, ?_⟩
    have := cs_bound xi k hk
    unfold J2
    linarith
  · obtain ⟨hmem, hdot⟩ := anti_unit xi
    refine ⟨_, hmem, J4_trivial _, ?_⟩
    unfold J2
    rw [hdot]
    linarith
  · obtain ⟨hmem, hdot⟩ := anti_unit xi
    apply not_stable_of xi0 xi 0 0 0 _ hmem
    right
    refine ⟨(J4_trivial _).le, ?_⟩
    unfold J2
    rw [hdot]
    linarith

theorem main (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm) :
      ((∀ u ∈ Iset eta00 eta E, 0 < fVal eta00 eta E u) →
          StrongStable eta00 eta E) ∧
      ((∃ u ∈ Iset eta00 eta E, fVal eta00 eta E u < 0) →
          ¬ Stable xi0 xi eta00 eta E) ∧
      (((∀ u ∈ Iset eta00 eta E, 0 ≤ fVal eta00 eta E u) ∧
        (∃ u ∈ Iset eta00 eta E, fVal eta00 eta E u = 0)) →
        ((∀ u ∈ Iset eta00 eta E, fVal eta00 eta E u = 0 →
            (Reg E u → 0 < gVal xi0 xi eta E u) ∧
            (¬ Reg E u → ∀ p : Fin 3 → ℝ, IsEigenProj E u xi p →
                0 < gVal xi0 xi eta E u - norm3 p * Real.sqrt (fPrimeVal eta E u))) →
              WeakStable xi0 xi eta00 eta E) ∧
        ((∃ u ∈ Iset eta00 eta E, fVal eta00 eta E u = 0 ∧
            ((Reg E u ∧ gVal xi0 xi eta E u < 0) ∨
             (¬ Reg E u ∧ ∃ p : Fin 3 → ℝ, IsEigenProj E u xi p ∧
                gVal xi0 xi eta E u - norm3 p * Real.sqrt (fPrimeVal eta E u) < 0))) →
              ¬ Stable xi0 xi eta00 eta E)) := by
  obtain ⟨Q, lam, hQ1, hQ2, hEQ⟩ := spec3 E hE
  obtain ⟨kmin, hkmin, hmin⟩ := exists_min eta00 eta E
  obtain ⟨umin, humin, hfmin, -, -⟩ :=
    bridge_fwd xi0 xi eta00 eta E hE Q lam hQ1 hQ2 hEQ kmin hkmin hmin
  have hJ4ge : ∀ k ∈ ballK, fVal eta00 eta E umin ≤ J4 eta00 eta E k := by
    intro k hk
    rw [hfmin]
    exact isMinOn_iff.mp hmin k hk
  have hwit : ∀ u ∈ Iset eta00 eta E, ∃ k ∈ ballK, J4 eta00 eta E k = fVal eta00 eta E u := by
    intro u hu
    by_cases hr : Reg E u
    · obtain ⟨k, hk, h1, -⟩ := bridge_bwd_reg xi0 xi eta00 eta E Q lam hQ1 hQ2 hEQ u hu hr
      exact ⟨k, hk, h1⟩
    · obtain ⟨p, hp⟩ := exists_eigenProj E Q lam hQ1 hQ2 hEQ u xi
      obtain ⟨k, hk, h1, -⟩ := bridge_bwd_irr xi0 xi eta00 eta E Q lam hQ1 hQ2 hEQ u hu hr p hp
      exact ⟨k, hk, h1⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hpos k hk
    exact lt_of_lt_of_le (hpos umin humin) (hJ4ge k hk)
  · rintro ⟨u, hu, hneg⟩
    obtain ⟨k, hk, h1⟩ := hwit u hu
    exact not_stable_of xi0 xi eta00 eta E k hk (Or.inl (h1 ▸ hneg))
  · rintro ⟨hnn, -⟩
    refine ⟨?_, ?_⟩
    · intro hcond k hk
      have h0 : 0 ≤ J4 eta00 eta E k := le_trans (hnn umin humin) (hJ4ge k hk)
      rcases h0.lt_or_eq with hlt | heq
      · exact Or.inl hlt
      · right
        refine ⟨heq.symm, ?_⟩
        have hmink : IsMinOn (J4 eta00 eta E) ballK k := by
          rw [isMinOn_iff]
          intro k' hk'
          rw [← heq]
          exact le_trans (hnn umin humin) (hJ4ge k' hk')
        obtain ⟨u, hu, hfu, hreg, hirr⟩ :=
          bridge_fwd xi0 xi eta00 eta E hE Q lam hQ1 hQ2 hEQ k hk hmink
        have hfu0 : fVal eta00 eta E u = 0 := hfu.trans heq.symm
        obtain ⟨hc1, hc2⟩ := hcond u hu hfu0
        by_cases hr : Reg E u
        · rw [← hreg hr]
          exact hc1 hr
        · obtain ⟨p, hp, hle⟩ := hirr hr
          exact lt_of_lt_of_le (hc2 hr p hp) hle
    · rintro ⟨u, hu, hfu0, hcase⟩
      rcases hcase with ⟨hr, hg⟩ | ⟨hr, p, hp, hg⟩
      · obtain ⟨k, hk, h1, h2⟩ := bridge_bwd_reg xi0 xi eta00 eta E Q lam hQ1 hQ2 hEQ u hu hr
        exact not_stable_of xi0 xi eta00 eta E k hk
          (Or.inr ⟨by rw [h1, hfu0], by rw [h2]; exact hg⟩)
      · obtain ⟨k, hk, h1, h2⟩ :=
          bridge_bwd_irr xi0 xi eta00 eta E Q lam hQ1 hQ2 hEQ u hu hr p hp
        exact not_stable_of xi0 xi eta00 eta E k hk
          (Or.inr ⟨by rw [h1, hfu0], by rw [h2]; exact hg⟩)

end THDMLib

set_option maxHeartbeats 4000000 in
open THDM in
theorem solution
    (xi0 : ℝ) (xi : Fin 3 → ℝ) (eta00 : ℝ) (eta : Fin 3 → ℝ)
    (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm) :
    (V4Trivial eta00 eta E →
        ((norm3 xi < xi0 → Stable xi0 xi eta00 eta E) ∧
         (xi0 = norm3 xi → MarginalCase xi0 xi eta00 eta E ∧ Stable xi0 xi eta00 eta E) ∧
         (xi0 < norm3 xi → ¬ Stable xi0 xi eta00 eta E))) ∧
    (¬ V4Trivial eta00 eta E →
      ((∀ u ∈ Iset eta00 eta E, 0 < fVal eta00 eta E u) →
          StrongStable eta00 eta E) ∧
      ((∃ u ∈ Iset eta00 eta E, fVal eta00 eta E u < 0) →
          ¬ Stable xi0 xi eta00 eta E) ∧
      (((∀ u ∈ Iset eta00 eta E, 0 ≤ fVal eta00 eta E u) ∧
        (∃ u ∈ Iset eta00 eta E, fVal eta00 eta E u = 0)) →
        ((∀ u ∈ Iset eta00 eta E, fVal eta00 eta E u = 0 →
            (Reg E u → 0 < gVal xi0 xi eta E u) ∧
            (¬ Reg E u → ∀ p : Fin 3 → ℝ, IsEigenProj E u xi p →
                0 < gVal xi0 xi eta E u - norm3 p * Real.sqrt (fPrimeVal eta E u))) →
              WeakStable xi0 xi eta00 eta E) ∧
        ((∃ u ∈ Iset eta00 eta E, fVal eta00 eta E u = 0 ∧
            ((Reg E u ∧ gVal xi0 xi eta E u < 0) ∨
             (¬ Reg E u ∧ ∃ p : Fin 3 → ℝ, IsEigenProj E u xi p ∧
                gVal xi0 xi eta E u - norm3 p * Real.sqrt (fPrimeVal eta E u) < 0))) →
              ¬ Stable xi0 xi eta00 eta E))) := by
  exact ⟨THDMLib.v4_part xi0 xi eta00 eta E, fun _ => THDMLib.main xi0 xi eta00 eta E hE⟩

