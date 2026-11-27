-- Prove2me | solution 1 for SystemicHoldings.FEfficient.Supplement.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:03:55.794493+00:00
-- url     : https://prove2.me/submissions/0259b9cf-287b-441d-a25a-2c9f771e7890

import Mathlib
import Definitions.Def_SystemicHoldings_FEfficient_Model
import Definitions.Def_SystemicHoldings_FEfficient_Supplement_Diversification

open SystemicHoldings
open SystemicHoldings.FEfficient
open SystemicHoldings.FEfficient.Supplement

open Matrix

/-- Theorem 4.2, p. 14 (Awiszus–Capponi–Weber, arXiv:2003.10121v3; proof E-Companion pp. 11–12):
under Assumption 2 (`σ_k > 0`), Assumption 3, `∑ q = ∑ b =: T` and `T ≠ 0`, full diversification
`Q^diversified = (1/T) q bᵀ` is f-efficient (Definition 1: feasible and MSD-minimal over `𝒟(q, b)`)
if and only if `q` and `z = G⁻¹ 1_K` are linearly dependent. -/
theorem solution {K N : ℕ} (μ σ : Fin K → ℝ) (hσ : ∀ k, 0 < σ k)
    (q : Fin K → ℝ) (b v : Fin N → ℝ)
    (hT : ∑ k, q k = ∑ i, b i) (hT0 : ∑ k, q k ≠ 0)
    (hA3 : Assumption3 b v) :
    IsFEfficient μ σ q b v (qDiversified q b) ↔
      ¬ LinearIndependent ℝ ![q, zVec μ σ] := by
        classical
        have hGv : ∀ x : Fin K → ℝ, shockMoment μ σ *ᵥ x = fun k => μ k * (μ ⬝ᵥ x) + σ k ^ 2 * x k := by
          intro x; funext k
          simp [shockMoment, mulVec, dotProduct, vecMulVec, diagonal, Finset.mul_sum, add_mul,
            Finset.sum_add_distrib, ite_mul, mul_assoc]
        have hB : ∀ x y : Fin K → ℝ, x ⬝ᵥ (shockMoment μ σ *ᵥ y)
            = (x ⬝ᵥ μ) * (μ ⬝ᵥ y) + ∑ k, σ k ^ 2 * x k * y k := by
          intro x y; rw [hGv]
          simp only [dotProduct, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
          congr 1
          · apply Finset.sum_congr rfl; intro k _; ring
          · apply Finset.sum_congr rfl; intro k _; ring
        have hsymm : ∀ x y : Fin K → ℝ, x ⬝ᵥ (shockMoment μ σ *ᵥ y) = y ⬝ᵥ (shockMoment μ σ *ᵥ x) := by
          intro x y
          rw [hB, hB, dotProduct_comm x μ, dotProduct_comm y μ, mul_comm (μ ⬝ᵥ x)]
          congr 1; apply Finset.sum_congr rfl; intro k _; ring
        have hpos : ∀ x : Fin K → ℝ, 0 ≤ x ⬝ᵥ (shockMoment μ σ *ᵥ x) := by
          intro x
          rw [hB, dotProduct_comm x μ]
          refine add_nonneg (mul_self_nonneg _) (Finset.sum_nonneg fun k _ => ?_)
          rw [show σ k ^ 2 * x k * x k = (σ k * x k) ^ 2 by ring]; positivity
        have hinj : ∀ x : Fin K → ℝ, shockMoment μ σ *ᵥ x = 0 → x = 0 := by
          intro x hx
          have h0 : x ⬝ᵥ (shockMoment μ σ *ᵥ x) = 0 := by rw [hx, dotProduct_zero]
          rw [hB, dotProduct_comm x μ] at h0
          have h1 : 0 ≤ (μ ⬝ᵥ x) * (μ ⬝ᵥ x) := mul_self_nonneg _
          have h2 : ∀ k ∈ (Finset.univ : Finset (Fin K)), 0 ≤ σ k ^ 2 * x k * x k := fun k _ => by
            rw [show σ k ^ 2 * x k * x k = (σ k * x k) ^ 2 by ring]; positivity
          have h3 := Finset.sum_nonneg h2
          have h4 : ∑ k, σ k ^ 2 * x k * x k = 0 := by linarith
          rw [Finset.sum_eq_zero_iff_of_nonneg h2] at h4
          funext k
          have h5 := h4 k (Finset.mem_univ _)
          have hs := hσ k
          have h6 : σ k * x k = 0 := by
            have : (σ k * x k) ^ 2 = 0 := by rw [← h5]; ring
            exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
          rcases mul_eq_zero.mp h6 with h | h
          · linarith
          · simpa using h
        have hdet : IsUnit (shockMoment μ σ).det := by
          rw [isUnit_iff_ne_zero]
          intro h
          obtain ⟨x, hx0, hx⟩ := exists_mulVec_eq_zero_iff.mpr h
          exact hx0 (hinj x hx)
        have hGz : shockMoment μ σ *ᵥ zVec μ σ = fun _ => (1 : ℝ) := by
          unfold zVec; rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
        have hexp : ∀ y d : Fin K → ℝ, (y + d) ⬝ᵥ (shockMoment μ σ *ᵥ (y + d))
            = y ⬝ᵥ (shockMoment μ σ *ᵥ y) + 2 * (d ⬝ᵥ (shockMoment μ σ *ᵥ y))
              + d ⬝ᵥ (shockMoment μ σ *ᵥ d) := by
          intro y d
          rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hsymm y d]; ring
        have hvm : ∀ (a : Fin K → ℝ) (w x : Fin N → ℝ), vecMulVec a w *ᵥ x = (w ⬝ᵥ x) • a := by
          intro a w x; funext k
          simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
        have hone : ∀ x : Fin K → ℝ, (fun _ => (1 : ℝ)) ⬝ᵥ x = ∑ k, x k := by
          intro x; simp [dotProduct]
        have honeN : ∀ x : Fin N → ℝ, x ⬝ᵥ (fun _ => (1 : ℝ)) = ∑ k, x k := by
          intro x; simp [dotProduct]
        have hQx : ∀ x : Fin N → ℝ, qDiversified q b *ᵥ x = ((b ⬝ᵥ x) / ∑ k, q k) • q := by
          intro x
          unfold qDiversified
          rw [smul_mulVec, hvm, smul_smul]; congr 1; ring
        have hxQ : (fun _ => (1 : ℝ)) ᵥ* qDiversified q b = b := by
          unfold qDiversified
          rw [vecMul_smul, vecMul_vecMulVec, hone, smul_smul, one_div, inv_mul_cancel₀ hT0, one_smul]
        have hfeas : qDiversified q b ∈ feasible q b := by
          refine ⟨?_, hxQ⟩
          rw [hQx, honeN, ← hT, div_self hT0, one_smul]
        have hsumQ : ∀ Q ∈ feasible q b, (fun _ => (1 : ℝ)) ⬝ᵥ (Q *ᵥ v) = b ⬝ᵥ v := by
          intro Q hQ
          rw [dotProduct_mulVec, hQ.2]
        set c : ℝ := (b ⬝ᵥ v) / ∑ k, q k with hc
        have hc0 : c ≠ 0 := div_ne_zero hA3.2 hT0
        set y : Fin K → ℝ := c • q with hy
        have hmsdD : msd μ σ v (qDiversified q b) = y ⬝ᵥ (shockMoment μ σ *ᵥ y) := by
          unfold msd; rw [hQx]
        have hsumy : (fun _ => (1 : ℝ)) ⬝ᵥ y = b ⬝ᵥ v := by
          rw [hy, dotProduct_smul, hone, smul_eq_mul, hc, div_mul_cancel₀ _ hT0]
        obtain ⟨k0, -, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT0
        constructor
        · rintro ⟨-, hmin⟩
          obtain ⟨⟨i, j, hij⟩, -⟩ := hA3
          have hvij : v i - v j ≠ 0 := sub_ne_zero.mpr hij
          set w : Fin N → ℝ := fun n => ((if n = i then 1 else 0) - (if n = j then 1 else 0)) / (v i - v j)
            with hw
          have hw1 : w ⬝ᵥ (fun _ => (1 : ℝ)) = 0 := by
            rw [honeN, hw]
            simp [← Finset.sum_div, Finset.sum_sub_distrib]
          have hwv : w ⬝ᵥ v = 1 := by
            rw [hw]
            simp only [dotProduct, div_mul_eq_mul_div, ← Finset.sum_div, sub_mul, Finset.sum_sub_distrib,
              ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
            exact div_self hvij
          have hkey : ∀ d : Fin K → ℝ, (fun _ => (1 : ℝ)) ⬝ᵥ d = 0 →
              0 ≤ 2 * (d ⬝ᵥ (shockMoment μ σ *ᵥ y)) + d ⬝ᵥ (shockMoment μ σ *ᵥ d) := by
            intro d hd
            have hQ' : qDiversified q b + vecMulVec d w ∈ feasible q b := by
              constructor
              · rw [add_mulVec, hfeas.1, hvm, hw1, zero_smul, add_zero]
              · rw [vecMul_add, hxQ, vecMul_vecMulVec, hd, zero_smul, add_zero]
            have h := hmin _ hQ'
            rw [hmsdD] at h
            unfold msd at h
            rw [add_mulVec, hvm, hwv, one_smul, hQx, ← hc, ← hy, hexp] at h
            linarith
          have horth : ∀ d : Fin K → ℝ, (fun _ => (1 : ℝ)) ⬝ᵥ d = 0 →
              d ⬝ᵥ (shockMoment μ σ *ᵥ y) = 0 := by
            intro d hd
            set a := d ⬝ᵥ (shockMoment μ σ *ᵥ y) with ha
            set e := d ⬝ᵥ (shockMoment μ σ *ᵥ d) with he
            have he0 : 0 ≤ e := hpos d
            have ht : ∀ t : ℝ, 0 ≤ 2 * (t * a) + t * (t * e) := by
              intro t
              have := hkey (t • d) (by rw [dotProduct_smul, hd, smul_zero])
              simpa [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, ha, he] using this
            set u := a / (e + 1) with hu
            have hau : a = u * (e + 1) := by rw [hu]; field_simp
            have h1 := ht (-u)
            rw [hau] at h1
            have h2 : u ^ 2 * (e + 2) ≤ 0 := by nlinarith
            have h3 : u ^ 2 ≤ 0 := by
              by_contra hh; push Not at hh; nlinarith
            have h4 : u = 0 := by nlinarith [sq_nonneg u]
            rw [hau, h4, zero_mul]
          have hconst : ∀ k, (shockMoment μ σ *ᵥ q) k = (shockMoment μ σ *ᵥ q) k0 := by
            intro k
            have hd := horth (fun n => (if n = k then 1 else 0) - (if n = k0 then 1 else 0)) (by
              rw [hone]; simp [Finset.sum_sub_distrib])
            have hd' : (shockMoment μ σ *ᵥ y) k - (shockMoment μ σ *ᵥ y) k0 = 0 := by
              rw [← hd]
              simp only [dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
                Finset.sum_ite_eq', Finset.mem_univ, if_true]
            rw [hy, mulVec_smul] at hd'
            simp only [Pi.smul_apply, smul_eq_mul] at hd'
            have : c * ((shockMoment μ σ *ᵥ q) k - (shockMoment μ σ *ᵥ q) k0) = 0 := by
              rw [mul_sub]; exact hd'
            rcases mul_eq_zero.mp this with h | h
            · exact absurd h hc0
            · linarith
          set lam := (shockMoment μ σ *ᵥ q) k0 with hlam
          have hqz : q = lam • zVec μ σ := by
            have : shockMoment μ σ *ᵥ (q - lam • zVec μ σ) = 0 := by
              rw [mulVec_sub, mulVec_smul, hGz]
              funext k
              simp [hconst k]
            exact sub_eq_zero.mp (hinj _ this)
          rw [LinearIndependent.pair_iff]
          intro h
          have := h 1 (-lam) (by rw [hqz, one_smul, neg_smul, add_neg_cancel])
          exact one_ne_zero this.1
        · intro hdep
          refine ⟨hfeas, fun Q' hQ' => ?_⟩
          rw [LinearIndependent.pair_iff] at hdep
          push Not at hdep
          obtain ⟨s, t, hst, hne⟩ := hdep
          have hGs : s • (shockMoment μ σ *ᵥ q) + t • (fun _ => (1 : ℝ)) = 0 := by
            rw [← hGz, ← mulVec_smul, ← mulVec_smul, ← mulVec_add, hst, mulVec_zero]
          have hs : s ≠ 0 := by
            intro hs0
            have ht := hne hs0
            rw [hs0] at hGs
            have := congrFun hGs k0
            simp at this
            exact ht this
          have hGq : ∀ k, (shockMoment μ σ *ᵥ q) k = -(t / s) := by
            intro k
            have := congrFun hGs k
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, Pi.zero_apply] at this
            field_simp
            linarith
          set d := Q' *ᵥ v - y with hd
          have hd1 : (fun _ => (1 : ℝ)) ⬝ᵥ d = 0 := by
            rw [hd, dotProduct_sub, hsumQ Q' hQ', hsumy, sub_self]
          have hdy : d ⬝ᵥ (shockMoment μ σ *ᵥ y) = 0 := by
            rw [hy, mulVec_smul, dotProduct_smul]
            have : d ⬝ᵥ (shockMoment μ σ *ᵥ q) = -(t / s) * ((fun _ => (1 : ℝ)) ⬝ᵥ d) := by
              rw [hone]; simp only [dotProduct, hGq, Finset.mul_sum]; apply Finset.sum_congr rfl
              intro k _; ring
            rw [this, hd1, mul_zero, smul_zero]
          rw [hmsdD]
          unfold msd
          have hQ'v : Q' *ᵥ v = y + d := by rw [hd]; abel
          rw [hQ'v, hexp, hdy]
          linarith [hpos d]
