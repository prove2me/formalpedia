-- Prove2me | solution 1 for WeierstrassEllipticZeta.complex_auxiliary_systems_of_bounded_grid_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T01:15:06.513448+00:00
-- url     : https://prove2.me/submissions/b2919912-1b1a-402c-b0fc-c8ad323969da

import Theorems.Thm_WeierstrassEllipticZeta_cleared_addition_jet_vanishing_iff
import Theorems.Thm_WeierstrassEllipticZeta_cleared_auxiliary_first_derivative
import Definitions.Def_WeierstrassEllipticZeta_GridJetMatrices
import Definitions.Def_TranscendenceTheory_ComplexAuxiliarySystem
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
set_option maxHeartbeats 1000000
open scoped Polynomial
open Filter WeierstrassEllipticZeta

private theorem p2m_grid_mono (ω u₁ u₂ : ℂ) (A B : Fin 3 → ℕ) (hAB : ∀ i, A i ≤ B i) :
    auxiliaryGrid u₁ u₂ ω A ⊆ auxiliaryGrid u₁ u₂ ω B := by
  intro v hv
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hv
  refine Finset.mem_image.mpr ⟨fun i => (t i).castLE (hAB i), Finset.mem_univ _, ?_⟩
  rfl

private theorem p2m_grid_regular (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (A : Fin 3 → ℕ) (v : ℂ) (hv : v ∈ auxiliaryGrid u₁ u₂ ω A) :
    u₁ / 2 ∉ L.lattice ∧ u₁ / 2 + v ∉ L.lattice ∧ u₁ / 2 - v ∉ L.lattice := by
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hv
  let m : Fin 3 → ℤ := fun i => (t i : ℕ)
  have hz : u₁ / 2 ∉ L.lattice := by
    simpa [integerGridPoint] using h_grid.shifted_regular (fun _ => 0)
  have hneg : integerGridPoint u₁ u₂ ω (fun i => -m i) =
      -integerGridPoint u₁ u₂ ω m := by
    simp only [integerGridPoint, Int.cast_neg]
    ring
  refine ⟨hz, ?_, ?_⟩
  · simpa only [add_comm] using h_grid.shifted_regular m
  · simpa only [hneg, sub_eq_add_neg, add_comm] using
      h_grid.shifted_regular (fun i => -m i)

private theorem p2m_bivariate_coeff_norm_le (p : ℤ[X][X]) (j k : ℕ) :
    ‖(p.coeff j).coeff k‖ ≤
      ((∑ a ∈ p.support, ∑ b ∈ (p.coeff a).support,
        ((p.coeff a).coeff b).natAbs) : ℝ) := by
  classical
  by_cases hj : j ∈ p.support
  · by_cases hk : k ∈ (p.coeff j).support
    · have h1 : ((p.coeff j).coeff k).natAbs ≤
          ∑ b ∈ (p.coeff j).support, ((p.coeff j).coeff b).natAbs :=
        Finset.single_le_sum (f := fun b => ((p.coeff j).coeff b).natAbs) (fun _ _ => Nat.zero_le _) hk
      have h2 : (∑ b ∈ (p.coeff j).support, ((p.coeff j).coeff b).natAbs) ≤
          ∑ a ∈ p.support, ∑ b ∈ (p.coeff a).support, ((p.coeff a).coeff b).natAbs :=
        Finset.single_le_sum (f := fun a => ∑ b ∈ (p.coeff a).support, ((p.coeff a).coeff b).natAbs) (fun _ _ => Nat.zero_le _) hj
      have h := h1.trans h2
      have hnorm : ‖(p.coeff j).coeff k‖ = (((p.coeff j).coeff k).natAbs : ℝ) := by
        simp only [Int.norm_eq_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
      rw [hnorm]
      exact_mod_cast h
    · rw [Polynomial.notMem_support_iff.mp hk, norm_zero]
      positivity
  · rw [Polynomial.notMem_support_iff.mp hj, Polynomial.coeff_zero, norm_zero]
    positivity

private theorem p2m_auxiliary_sum_deriv (L : PeriodPair)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    {ι : Type} [Fintype ι] (c : ι → ℂ) (d e f : ι → ℕ)
    (x : ℂ) (hx : x ∉ L.lattice) (n : ℕ) :
    iteratedDeriv n (fun w => ∑ i, c i * w ^ d i * L.weierstrassP w ^ e i *
      weierstrassZeta L w ^ f i) x =
      ∑ i, c i * iteratedDeriv n (fun w => w ^ d i * L.weierstrassP w ^ e i *
        weierstrassZeta L w ^ f i) x := by
  have hZ : AnalyticOnNhd ℂ (weierstrassZeta L) L.latticeᶜ :=
    (show DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ from
      fun z hz => (h_zeta_deriv z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
        L.isClosed_lattice.isOpen_compl
  have hm (i : ι) : AnalyticAt ℂ (fun w => w ^ d i * L.weierstrassP w ^ e i *
      weierstrassZeta L w ^ f i) x :=
    ((analyticAt_id.pow _).mul ((L.analyticOnNhd_weierstrassP _ hx).pow _)).mul
      ((hZ _ hx).pow _)
  have heq : (fun w => ∑ i, c i * w ^ d i * L.weierstrassP w ^ e i *
      weierstrassZeta L w ^ f i) =
      fun w => ∑ i, c i * (w ^ d i * L.weierstrassP w ^ e i * weierstrassZeta L w ^ f i) := by
    funext w
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq, iteratedDeriv_fun_sum (f := fun i w => c i *
    (w ^ d i * L.weierstrassP w ^ e i * weierstrassZeta L w ^ f i))
    (fun i _ => (analyticAt_const.mul (hm i)).contDiffAt)]
  apply Finset.sum_congr rfl
  intro i _
  exact iteratedDeriv_const_mul_field _ _

private theorem p2m_cleared_sum_deriv (L : PeriodPair)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    {ι : Type} [Fintype ι] (c : ι → ℂ) (d e f : ι → ℕ) (M : ℕ)
    (v z : ℂ) (hv : v ∉ L.lattice) (hz : z ∉ L.lattice) (hp : z + v ∉ L.lattice)
    (n : ℕ) :
    iteratedDeriv n (clearedAuxiliarySum L v c d e f M) z =
      ∑ i, c i * iteratedDeriv n (clearedAdditionMonomial L v M (d i) (e i) (f i)) z := by
  have hm (i : ι) : AnalyticAt ℂ (clearedAdditionMonomial L v M (d i) (e i) (f i)) z := by
    have h := (cleared_auxiliary_first_derivative L h_zeta_deriv v hv
      (fun _ : Unit => (1 : ℂ)) (fun _ => d i) (fun _ => e i) (fun _ => f i) M z hz hp).1
    have heq : clearedAuxiliarySum L v (fun _ : Unit => (1 : ℂ))
        (fun _ => d i) (fun _ => e i) (fun _ => f i) M =
        clearedAdditionMonomial L v M (d i) (e i) (f i) := by
      funext w
      simp only [WeierstrassEllipticZeta.clearedAuxiliarySum, Fintype.sum_unique, one_mul]
    rw [heq] at h
    exact h
  change iteratedDeriv n (fun w => ∑ i, c i *
    clearedAdditionMonomial L v M (d i) (e i) (f i) w) z = _
  rw [iteratedDeriv_fun_sum
    (f := fun i w => c i * clearedAdditionMonomial L v M (d i) (e i) (f i) w)
    (fun i _ => (analyticAt_const.mul (hm i)).contDiffAt)]
  apply Finset.sum_congr rfl
  intro i _
  exact iteratedDeriv_const_mul_field _ _


private theorem p2m_assemble_finite_matrices {ρ τ ι : Type} [Fintype ρ] [Fintype τ] [Fintype ι]
    (θ ν : ℂ) (a b c : ℝ) (N D E : ℕ)
    (hcols : 0 < Fintype.card ι) (hgap : 8 * Fintype.card ρ ≤ Fintype.card ι)
    (hD : (D : ℝ) ≤ a * N) (hE : (E : ℝ) ≤ a * N)
    (hsize : (Fintype.card ι : ℝ) * (E + 1) * (D + 1) ≤ Real.exp (a * N))
    (M : ρ → ι → ℤ[X][X]) (T : τ → ι → ℤ[X][X])
    (hM : ∀ r i, (M r i).natDegree ≤ E ∧
      (∀ j, ((M r i).coeff j).natDegree ≤ D) ∧
      ∀ j k, ‖((M r i).coeff j).coeff k‖ ≤ Real.exp (a * N))
    (hT : ∀ r i, (T r i).natDegree ≤ E ∧
      (∀ j, ((T r i).coeff j).natDegree ≤ D) ∧
      ∀ j k, ‖((T r i).coeff j).coeff k‖ ≤ Real.exp (a * N))
    (hsmall : ∀ z : ι → ℂ, z ≠ 0 →
      (∀ i, ‖z i‖ ≤ Real.exp (b * N)) →
      (∀ r, ∑ i, (M r i).eval₂ (Polynomial.aeval θ).toRingHom ν * z i = 0) →
      ∃ r : τ, (∑ i, (T r i).eval₂ (Polynomial.aeval θ).toRingHom ν * z i) ≠ 0 ∧
        ‖∑ i, (T r i).eval₂ (Polynomial.aeval θ).toRingHom ν * z i‖ ≤
          Real.exp (-c * (N : ℝ) ^ 2 * Real.log N)) :
    ∃ S : TranscendenceTheory.ComplexAuxiliarySystem θ ν a b c N, S.yDegree = E := by
  classical
  let eI := Fintype.equivFin ι
  let eM := Fintype.equivFin ρ
  let eT := Fintype.equivFin τ
  refine ⟨{
    rows := Fintype.card ρ
    cols := Fintype.card ι
    tests := Fintype.card τ
    xDegree := D
    yDegree := E
    cols_pos := hcols
    dimension_gap := hgap
    xDegree_le := hD
    yDegree_le := hE
    size_le := hsize
    equations := fun r i => M (eM.symm r) (eI.symm i)
    testForms := fun r i => T (eT.symm r) (eI.symm i)
    equations_yDegree := fun r i => (hM _ _).1
    equations_xDegree := fun r i => (hM _ _).2.1
    equations_height := fun r i => (hM _ _).2.2
    testForms_yDegree := fun r i => (hT _ _).1
    testForms_xDegree := fun r i => (hT _ _).2.1
    testForms_height := fun r i => (hT _ _).2.2
    small_nonzero := ?_ }, rfl⟩
  intro z hz hbound heq
  let w : ι → ℂ := fun i => z (eI i)
  have hw : w ≠ 0 := by
    intro h
    apply hz
    funext i
    simpa only [w, eI.apply_symm_apply, Pi.zero_apply] using congrFun h (eI.symm i)
  have hsum (p : ι → ℤ[X][X]) :
      (∑ i, (p i).eval₂ (Polynomial.aeval θ).toRingHom ν * w i) =
        ∑ i, (p (eI.symm i)).eval₂ (Polynomial.aeval θ).toRingHom ν * z i := by
    exact Fintype.sum_equiv eI _ _ (fun i => by simp only [w, eI.symm_apply_apply])
  obtain ⟨r, hr0, hrsmall⟩ := hsmall w hw (fun i => hbound (eI i)) (by
    intro r
    rw [hsum]
    simpa only [eM.symm_apply_apply] using heq (eM r))
  refine ⟨eT r, ?_, ?_⟩
  · simpa only [hsum, eT.symm_apply_apply] using hr0
  · simpa only [hsum, eT.symm_apply_apply] using hrsmall

theorem solution
    (L : PeriodPair) (ω u₁ u₂ θ ν : ℂ) (g : ℤ[X][X]) (d : ℤ[X])
    (hg : 0 < g.natDegree) (hd : Polynomial.aeval θ d ≠ 0)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_zeta_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (h_grid_matrices : AuxiliaryGridJetMatrixData L ω u₁ u₂ θ ν g d)
    (h_period_decay : ∀ B K : ℝ, 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∀ i, ‖c i‖ ≤ Real.exp (B * N)) →
        let f : ℂ → ℂ := fun z => ∑ i, c i * z ^ i.1.val *
          L.weierstrassP z ^ i.2.1.val * weierstrassZeta L z ^ i.2.2.val
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω
            ![auxiliaryS N, auxiliaryS N, auxiliaryS3 N],
          ∀ j < m + 1, iteratedDeriv j f x = 0) →
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω
            ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
          v ∈ L.lattice → ∀ n : ℕ, (n : ℝ) ≤ K * m →
            (∀ j < n, iteratedDeriv j f (u₁ / 2 + v) = 0) →
            ‖(Polynomial.aeval θ d) ^ (7 * (m + 2 * l + n)) * iteratedDeriv n f (u₁ / 2 + v)‖ ≤
              Real.exp (-(N : ℝ) ^ 2 * Real.log N / 147456))
    (h_arithmetic_nonlattice_decay : ∀ (C : ℕ) (B K : ℝ), 0 ≤ B → 0 < K → ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      let s := auxiliaryS N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        (∑ i, ‖c i‖) ≤ Real.exp (B * N) →
        let F : ℂ → ℂ := fun w => ∑ i, c i * w ^ i.1.val *
          L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val
        (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω ![s, s, auxiliaryS3 N],
          ∀ j < m + 1, iteratedDeriv j F x = 0) →
        ∀ v ∈ auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * auxiliaryS3 N],
          v ∉ L.lattice →
            ∀ P : NonlatticeCoordinatePresentation L θ ν v (u₁ / 2) C N s,
              ∀ n : ℕ, (n : ℝ) ≤ K * m →
                (∀ j < n, iteratedDeriv j F (u₁ / 2 + v) = 0) →
                ‖(∏ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν]
                    (P.denominator a) ^ nonlatticeJetWeight m l n a) *
                  (2 * (L.weierstrassP v - L.weierstrassP (u₁ / 2))) ^ (3 * l) *
                  iteratedDeriv n F (u₁ / 2 + v)‖ ≤
                    Real.exp (-(N : ℝ) ^ 2 * Real.log N / 147456))
    (h_escape : ∃ K : ℕ, 1 ≤ K ∧ ∀ᶠ N : ℕ in Filter.atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      ∀ c : Fin (m + 1) × Fin (l + 1) × Fin (l + 1) → ℂ,
        c ≠ 0 → ∃ v ∈ auxiliaryGrid u₁ u₂ ω
          ![3 * auxiliaryS N, 3 * auxiliaryS N, 3 * auxiliaryS3 N],
          ∃ n : ℕ, n ≤ K * m ∧
            iteratedDeriv n (fun w => ∑ i, c i * w ^ i.1.val *
              L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val)
                (u₁ / 2 + v) ≠ 0) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∃ S : TranscendenceTheory.ComplexAuxiliarySystem
          θ ν a ((3 + ‖θ‖ + ‖ν‖) * a) c N,
          S.yDegree < g.natDegree := by
  classical
  obtain ⟨K, hK, hescape⟩ := h_escape
  obtain ⟨C, hmat⟩ := h_grid_matrices
  obtain ⟨A₀, hA₀, hmat₀⟩ := hmat 1
  obtain ⟨A₁, hA₁, hmat₁⟩ := hmat K
  let a := A₀ + A₁ + 1
  let b := (3 + ‖θ‖ + ‖ν‖) * a
  have ha : 0 < a := by dsimp [a]; positivity
  have h1a : 1 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hA₀a : A₀ ≤ a := by dsimp [a]; linarith
  have hA₁a : A₁ ≤ a := by dsimp [a]; linarith
  have hKr : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  refine ⟨a, 1 / 147456, ha, by norm_num, ?_⟩
  filter_upwards [hmat₀, hmat₁, hescape, h_parameters 1 zero_lt_one, hlog,
    eventually_ge_atTop g.natDegree,
    h_period_decay b K hb hKr,
    h_arithmetic_nonlattice_decay C (A₁ + b) K (by positivity) hKr]
    with N h₀ h₁ he hpar hlogN hgN hpdec hndec
  let m := auxiliaryL0 N
  let l := auxiliaryL N
  let s := auxiliaryS N
  let q := auxiliaryS3 N
  let Γ := auxiliaryGrid u₁ u₂ ω ![s, s, q]
  let Γ₃ := auxiliaryGrid u₁ u₂ ω ![3 * s, 3 * s, 3 * q]
  let I := Fin (m + 1) × Fin (l + 1) × Fin (l + 1)
  obtain ⟨D₀, R₀, Q₀, hD₀, hsize₀, hgap, hR₀, hp₀, hn₀, hker₀⟩ := h₀
  obtain ⟨D₁, R₁, Q₁, hD₁, hsize₁, _, hR₁, hp₁, hn₁, hker₁⟩ := h₁
  let D := max D₀ D₁
  let E := g.natDegree - 1
  have hD₀D : D₀ ≤ D := le_max_left _ _
  have hD₁D : D₁ ≤ D := le_max_right _ _
  have hcI : Fintype.card I = (m + 1) * (l + 1) ^ 2 := by
    simp [I, Fintype.card_prod, pow_two]
  have hsub : Γ ⊆ Γ₃ := p2m_grid_mono ω u₁ u₂ _ _ (by
    intro i
    fin_cases i <;> simp <;> omega)
  let incl : Γ → Γ₃ := fun v => ⟨v.val, hsub v.property⟩
  let castOrder : Fin (m + 1) → Fin (1 * m + 1) := fun n =>
    ⟨n.val, by simpa only [one_mul] using n.isLt⟩
  let M : (Γ × Fin (m + 1)) → I → ℤ[X][X] := fun r i => R₀ (incl r.1) (castOrder r.2) i
  let T : (Γ₃ × Fin (K * m + 1)) → I → ℤ[X][X] := fun r i => R₁ r.1 r.2 i
  have hml : (m : ℝ) * Real.log N ≤ N := hpar.2.2.2.2.2.2.2.2.1
  have hmN : (m : ℝ) ≤ N := by
    have h := mul_le_mul_of_nonneg_left hlogN (Nat.cast_nonneg m)
    nlinarith only [h, hml]
  have he₀ : Real.exp (A₀ * N) ≤ Real.exp (a * N) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hA₀a (Nat.cast_nonneg N))
  have he₁ : Real.exp (A₁ * N) ≤ Real.exp (a * N) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hA₁a (Nat.cast_nonneg N))
  have hDN : (D : ℝ) ≤ a * N := by
    have h0 := hD₀.trans ((mul_le_mul_of_nonneg_left hmN hA₀.le).trans
      (mul_le_mul_of_nonneg_right hA₀a (Nat.cast_nonneg N)))
    have h1 := hD₁.trans ((mul_le_mul_of_nonneg_left hmN hA₁.le).trans
      (mul_le_mul_of_nonneg_right hA₁a (Nat.cast_nonneg N)))
    exact_mod_cast max_le h0 h1
  have hEN : (E : ℝ) ≤ a * N := by
    have h0 : E ≤ N := (Nat.sub_le _ _).trans hgN
    have h1 := mul_le_mul_of_nonneg_right h1a (Nat.cast_nonneg N)
    have h0' : (E : ℝ) ≤ N := by exact_mod_cast h0
    nlinarith only [h0', h1]
  have hsizeD : (Fintype.card I : ℝ) * (g.natDegree + 1) * (D + 1) ≤
      Real.exp (a * N) := by
    rw [hcI]
    push_cast
    rcases le_total D₀ D₁ with h | h
    · simpa only [D, max_eq_right h] using hsize₁.trans he₁
    · simpa only [D, max_eq_left h] using hsize₀.trans he₀
  have hsize : (Fintype.card I : ℝ) * (E + 1) * (D + 1) ≤ Real.exp (a * N) := by
    apply le_trans ?_ hsizeD
    gcongr
    exact_mod_cast Nat.sub_le g.natDegree 1
  have hcard : (Fintype.card I : ℝ) ≤ Real.exp (A₁ * N) := by
    calc
      _ = (Fintype.card I : ℝ) * 1 * 1 := by ring
      _ ≤ (Fintype.card I : ℝ) * (g.natDegree + 1) * (D₁ + 1) := by
        gcongr <;> linarith [(Nat.cast_nonneg g.natDegree : (0 : ℝ) ≤ g.natDegree), (Nat.cast_nonneg D₁ : (0 : ℝ) ≤ D₁)]
      _ ≤ Real.exp (A₁ * N) := by
        simpa only [hcI, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hsize₁
  have hM : ∀ r i, (M r i).natDegree ≤ E ∧
      (∀ j, ((M r i).coeff j).natDegree ≤ D) ∧
      ∀ j k, ‖((M r i).coeff j).coeff k‖ ≤ Real.exp (a * N) := by
    intro r i
    obtain ⟨hy, hx, hh⟩ := hR₀ (incl r.1) (castOrder r.2) i
    exact ⟨Nat.le_sub_one_of_lt hy, fun j => (hx j).trans hD₀D,
      fun j k => (p2m_bivariate_coeff_norm_le _ j k).trans (hh.trans he₀)⟩
  have hT : ∀ r i, (T r i).natDegree ≤ E ∧
      (∀ j, ((T r i).coeff j).natDegree ≤ D) ∧
      ∀ j k, ‖((T r i).coeff j).coeff k‖ ≤ Real.exp (a * N) := by
    intro r i
    obtain ⟨hy, hx, hh⟩ := hR₁ r.1 r.2 i
    exact ⟨Nat.le_sub_one_of_lt hy, fun j => (hx j).trans hD₁D,
      fun j k => (p2m_bivariate_coeff_norm_le _ j k).trans (hh.trans he₁)⟩
  have hsmall : ∀ c : I → ℂ, c ≠ 0 →
      (∀ i, ‖c i‖ ≤ Real.exp (b * N)) →
      (∀ r, ∑ i, (M r i).eval₂ (Polynomial.aeval θ).toRingHom ν * c i = 0) →
      ∃ r : Γ₃ × Fin (K * m + 1),
        (∑ i, (T r i).eval₂ (Polynomial.aeval θ).toRingHom ν * c i) ≠ 0 ∧
        ‖∑ i, (T r i).eval₂ (Polynomial.aeval θ).toRingHom ν * c i‖ ≤
          Real.exp (-(1 / 147456) * (N : ℝ) ^ 2 * Real.log N) := by
    intro c hc hcb hceq
    let F : ℂ → ℂ := fun w => ∑ i, c i * w ^ i.1.val *
      L.weierstrassP w ^ i.2.1.val * weierstrassZeta L w ^ i.2.2.val
    have hzero : ∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω ![s, s, q],
        ∀ j < m + 1, iteratedDeriv j F x = 0 := by
      intro x hx j hj
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      have hker := (hker₀ (incl ⟨v, hv⟩) c).mp (by
        intro n
        let ni : Fin (m + 1) := ⟨n.val, by simpa only [one_mul] using n.isLt⟩
        exact hceq (⟨v, hv⟩, ni))
      simpa only [incl, add_comm] using hker j (by simpa only [one_mul] using (Nat.le_of_lt_succ hj))
    have hsumc : (∑ i, ‖c i‖) ≤ Real.exp ((A₁ + b) * N) := by
      calc
        _ ≤ ∑ i : I, Real.exp (b * N) := Finset.sum_le_sum (fun i _ => hcb i)
        _ = (Fintype.card I : ℝ) * Real.exp (b * N) := by simp
        _ ≤ Real.exp (A₁ * N) * Real.exp (b * N) :=
          mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
        _ = Real.exp ((A₁ + b) * N) := by rw [← Real.exp_add]; congr 1; ring
    obtain ⟨v, hv, n', hn', hne'⟩ := he c hc
    have hex : ∃ n : ℕ, n ≤ K * m ∧ iteratedDeriv n F (u₁ / 2 + v) ≠ 0 :=
      ⟨n', hn', hne'⟩
    let n := Nat.find hex
    have hn : n ≤ K * m := (Nat.find_spec hex).1
    have hne : iteratedDeriv n F (u₁ / 2 + v) ≠ 0 := (Nat.find_spec hex).2
    have hbefore : ∀ j < n, iteratedDeriv j F (u₁ / 2 + v) = 0 := by
      intro j hj
      by_contra h
      exact Nat.find_min hex hj ⟨(Nat.le_of_lt hj).trans hn, h⟩
    have hnr : (n : ℝ) ≤ (K : ℝ) * m := by exact_mod_cast hn
    let vi : Γ₃ := ⟨v, hv⟩
    let ni : Fin (K * m + 1) := ⟨n, by omega⟩
    obtain ⟨hz, hplus, hminus⟩ := p2m_grid_regular L ω u₁ u₂ h_grid _ v hv
    refine ⟨(vi, ni), ?_⟩
    by_cases hvL : v ∈ L.lattice
    · have hrow : (∑ i, (T (vi, ni) i).eval₂ (Polynomial.aeval θ).toRingHom ν * c i) =
          (Polynomial.aeval θ d) ^ (7 * (m + 2 * l + n)) * iteratedDeriv n F (u₁ / 2 + v) := by
        rw [p2m_auxiliary_sum_deriv L h_zeta_deriv c (fun i => i.1.val)
          (fun i => i.2.1.val) (fun i => i.2.2.val) _ hplus n, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [show (T (vi, ni) i).eval₂ (Polynomial.aeval θ).toRingHom ν = _ from hp₁ vi hvL ni i]
        dsimp only [ni, Fin.val_mk]
        ring
      rw [hrow]
      refine ⟨mul_ne_zero (pow_ne_zero _ hd) hne, ?_⟩
      convert hpdec c hcb hzero v hv hvL n hnr hbefore using 1
      congr 1
      ring
    · let P := Q₁ vi hvL
      let δ : ℂ := ∏ a, MvPolynomial.eval₂ (Int.castRingHom ℂ) ![θ, ν]
        (P.denominator a) ^ nonlatticeJetWeight m l n a
      let α : ℂ := (2 * (L.weierstrassP v - L.weierstrassP (u₁ / 2))) ^ (3 * l)
      have hδ : δ ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun a _ =>
        pow_ne_zero _ (P.denominator_ne_zero a))
      have hα : α ≠ 0 :=
        (cleared_addition_jet_vanishing_iff L h_zeta_deriv h_zeta_addition
          (u₁ / 2) v hz hvL hplus hminus l 0
          (fun i : I => i.1.val) (fun i => i.2.1.val) (fun i => i.2.2.val) c).1
      have hrow : (∑ i, (T (vi, ni) i).eval₂ (Polynomial.aeval θ).toRingHom ν * c i) =
          δ * α * iteratedDeriv n F (u₁ / 2 + v) := by
        have hid := (cleared_auxiliary_first_derivative L h_zeta_deriv v hvL c
          (fun i => i.1.val) (fun i => i.2.1.val) (fun i => i.2.2.val) l
          (u₁ / 2) hz hplus).2 n hbefore
        calc
          _ = δ * iteratedDeriv n (clearedAuxiliarySum L v c
              (fun i => i.1.val) (fun i => i.2.1.val) (fun i => i.2.2.val) l) (u₁ / 2) := by
            rw [p2m_cleared_sum_deriv L h_zeta_deriv c (fun i => i.1.val)
              (fun i => i.2.1.val) (fun i => i.2.2.val) l v (u₁ / 2) hvL hz hplus n,
              Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [show (T (vi, ni) i).eval₂ (Polynomial.aeval θ).toRingHom ν = _ from hn₁ vi hvL ni i]
            dsimp only [δ, P, ni, Fin.val_mk]
            ring
          _ = _ := by rw [hid]; ring
      rw [hrow]
      refine ⟨mul_ne_zero (mul_ne_zero hδ hα) hne, ?_⟩
      convert hndec c hsumc hzero v hv hvL P n hnr hbefore using 1
      congr 1
      ring
  obtain ⟨S, hSE⟩ := p2m_assemble_finite_matrices θ ν a b (1 / 147456) N D E
    (by rw [hcI]; positivity)
    (by simpa only [hcI, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin,
      Nat.mul_comm Γ.card (m + 1)] using hgap)
    hDN hEN hsize M T hM hT hsmall
  exact ⟨S, hSE.trans_lt (Nat.sub_lt hg (by norm_num))⟩
