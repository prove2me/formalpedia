-- Prove2me | solution 1 for OptInapprox.Bal2Sat.Supplement.proposition_11_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:41.059926+00:00
-- url     : https://prove2.me/submissions/c426d2a8-1f75-4caa-b0c0-f2a4907546f7

import Mathlib
import Definitions.Def_OptInapprox_Bal2Sat_Supplement_Qary

open OptInapprox
open OptInapprox.Bal2Sat
open OptInapprox.Bal2Sat.Supplement

theorem solution (q : ℕ) (hq : 2 ≤ q) (n d : ℕ)
    (ρ : ℝ) (hρ : -(1 / ((q : ℝ) - 1)) ≤ ρ ∧ ρ ≤ 1)
    (f : QCube q n → Fin d → ℝ) :
    qNoise ρ f = fun x j =>
      ∑ S : Finset (Fin n), ρ ^ S.card * subsetComponent f S x j := by
        classical
        have hq0 : (q:ℝ) ≠ 0 := by
          have : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
          exact this.ne'
        obtain ⟨L, hL⟩ : ∃ L : Finset (Fin n) → QCube q n → QCube q n → ℝ,
            L = fun S x y => (∏ k ∈ S, ((if x k = y k then (1:ℝ) else 0) - (q:ℝ)⁻¹)) *
              ∏ k ∈ Finset.univ \ S, (q:ℝ)⁻¹ := ⟨_, rfl⟩
        obtain ⟨P, hP⟩ : ∃ P : Finset (Fin n) → QCube q n → Fin d → ℝ,
            P = fun S x j => ∑ y, L S x y * f y j := ⟨_, rfl⟩
        have hexp : ∀ ρ' : ℝ, qNoise ρ' f = fun x j => ∑ S : Finset (Fin n), ρ' ^ S.card * P S x j := by
          intro ρ'
          funext x j
          have hk : ∀ y, qKernel ρ' x y = ∑ S : Finset (Fin n), ρ' ^ S.card * L S x y := by
            intro y
            unfold qKernel coordKernel
            have : ∀ k, ρ' * (if x k = y k then (1:ℝ) else 0) + (1 - ρ') / q
                = ρ' * ((if x k = y k then (1:ℝ) else 0) - (q:ℝ)⁻¹) + (q:ℝ)⁻¹ := by
              intro k; field_simp; ring
            simp_rw [this]
            rw [Finset.prod_add, Finset.powerset_univ]
            refine Finset.sum_congr rfl (fun S _ => ?_)
            rw [hL, Finset.prod_mul_distrib, Finset.prod_const]; ring
          simp only [qNoise, hk, hP, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun y _ => by ring))
        have hone : ∀ x j, ∑ S : Finset (Fin n), P S x j = f x j := by
          intro x j
          have := congrFun (congrFun (hexp 1) x) j
          simp only [one_pow, one_mul] at this
          rw [← this]
          simp only [qNoise, qKernel, coordKernel, one_mul, sub_self, zero_div, add_zero]
          rw [Finset.sum_eq_single x]
          · simp
          · intro y _ hy
            obtain ⟨k, hk⟩ : ∃ k, x k ≠ y k := by
              by_contra h; push Not at h; exact hy (funext h).symm
            rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk]), zero_mul]
          · simp
        have hCo : ∀ (i : Fin n) (b : Fin q) (h : QCube q n → ℝ), (∀ x a, h (Function.update x i a) = h x) →
            ∑ x, (if x i = b then (1:ℝ) else 0) * h x = (q:ℝ)⁻¹ * ∑ x, h x := by
          intro i b h hh
          have hc : ∀ c : Fin q, ∑ x, (if x i = c then (1:ℝ) else 0) * h x
              = ∑ x, (if x i = b then (1:ℝ) else 0) * h x := by
            intro c
            let e : QCube q n ≃ QCube q n :=
              Equiv.piCongrRight (fun k => if k = i then Equiv.swap b c else Equiv.refl (Fin q))
            have he : ∀ x, e x = Function.update x i (Equiv.swap b c (x i)) := by
              intro x; funext k
              by_cases hk : k = i
              · subst hk; simp [e]
              · simp [e, hk]
            rw [← Equiv.sum_comp e]
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [he, hh, Function.update_self]
            congr 1
            simp [Equiv.swap_apply_eq_iff]
          have hsum : ∑ x, h x = ∑ c : Fin q, ∑ x, (if x i = c then (1:ℝ) else 0) * h x := by
            rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [← Finset.sum_mul]; simp
          rw [hsum]; simp_rw [hc]; simp; field_simp
        have hC : ∀ (S U : Finset (Fin n)) (i : Fin n), i ∈ S → i ∉ U → ∀ g : QCube q n → ℝ,
            (∀ x y : QCube q n, (∀ k ∈ U, x k = y k) → g x = g y) → ∀ z, ∑ x, L S x z * g x = 0 := by
          intro S U i hiS hiU g hg z
          set M : QCube q n → ℝ := fun x => (∏ k ∈ S.erase i, ((if x k = z k then (1:ℝ) else 0) - (q:ℝ)⁻¹)) *
              ∏ k ∈ Finset.univ \ S, (q:ℝ)⁻¹ with hM
          have hLM : ∀ x, L S x z * g x = (if x i = z i then (1:ℝ) else 0) * (M x * g x) - (q:ℝ)⁻¹ * (M x * g x) := by
            intro x; rw [hL, hM]; dsimp only; rw [← Finset.mul_prod_erase S _ hiS]; ring
          have hind : ∀ x a, M (Function.update x i a) * g (Function.update x i a) = M x * g x := by
            intro x a
            congr 1
            · simp only [hM]; congr 1; refine Finset.prod_congr rfl (fun k hk => ?_)
              rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
            · apply hg; intro k hk; rw [Function.update_of_ne]; rintro rfl; exact hiU hk
          have := hCo i (z i) (fun x => M x * g x) hind
          simp_rw [hLM, Finset.sum_sub_distrib, this, ← Finset.mul_sum]; ring
        have hinner : ∀ (u : QSpace q n d) (S : Finset (Fin n)),
            inner ℝ u (WithLp.toLp 2 (fun p : QCube q n × Fin d => P S p.1 p.2))
              = ∑ j, ∑ y, f y j * ∑ x, L S x y * u (x,j) := by
          intro u S
          rw [PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          simp [hP, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
          ring
        have horth : ∀ (S U : Finset (Fin n)), ¬ S ⊆ U → ∀ u ∈ dependentSpace q n d U,
            inner ℝ u (WithLp.toLp 2 (fun p : QCube q n × Fin d => P S p.1 p.2)) = 0 := by
          intro S U hSU u hu
          obtain ⟨i, hiS, hiU⟩ := Finset.not_subset.mp hSU
          rw [hinner]
          refine Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun y _ => ?_))
          rw [hC S U i hiS hiU (fun x => u (x,j)) (fun x y hxy => hu x y hxy j) y, mul_zero]
        have hmemD : ∀ S, WithLp.toLp 2 (fun p : QCube q n × Fin d => P S p.1 p.2) ∈ dependentSpace q n d S := by
          intro S x y hxy j
          show P S x j = P S y j
          rw [hP]; dsimp only
          refine Finset.sum_congr rfl (fun z _ => ?_)
          rw [hL]; dsimp only
          congr 2
          exact Finset.prod_congr rfl (fun k hk => by rw [hxy k hk])
        have hmain : ∀ S, subsetComponent f S = P S := by
          intro S
          have key : (subsetSpace q n d S).starProjection
              (WithLp.toLp 2 (fun p : QCube q n × Fin d => f p.1 p.2))
              = WithLp.toLp 2 (fun p : QCube q n × Fin d => P S p.1 p.2) := by
            apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
            · refine ⟨hmemD S, ?_⟩
              show _ ∈ (⨆ T : {T : Finset (Fin n) // T ⊂ S}, dependentSpace q n d T.val)ᗮ
              rw [Submodule.mem_orthogonal]
              intro u hu
              refine Submodule.iSup_induction _
                (motive := fun u => inner ℝ u (WithLp.toLp 2 (fun p : QCube q n × Fin d => P S p.1 p.2)) = 0)
                hu ?_ ?_ ?_
              · rintro ⟨T, hT⟩ u hu
                exact horth S T (fun h => hT.2 h) u hu
              · simp
              · intro a b ha hb; rw [inner_add_left, ha, hb, add_zero]
            · intro w hw
              have hv : WithLp.toLp 2 (fun p : QCube q n × Fin d => f p.1 p.2)
                  - WithLp.toLp 2 (fun p : QCube q n × Fin d => P S p.1 p.2)
                  = ∑ S' ∈ Finset.univ.erase S, WithLp.toLp 2 (fun p : QCube q n × Fin d => P S' p.1 p.2) := by
                ext ⟨x, j⟩
                simp only [WithLp.ofLp_sub, WithLp.ofLp_sum, Pi.sub_apply, Finset.sum_apply]
                rw [← hone x j, ← Finset.add_sum_erase _ _ (Finset.mem_univ S)]
                simp
              rw [hv, sum_inner]
              refine Finset.sum_eq_zero (fun S' hS' => ?_)
              rw [real_inner_comm]
              by_cases hsub : S' ⊆ S
              · have hss : S' ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Finset.ne_of_mem_erase hS'⟩
                have hmem : WithLp.toLp 2 (fun p : QCube q n × Fin d => P S' p.1 p.2) ∈
                    ⨆ T : {T : Finset (Fin n) // T ⊂ S}, dependentSpace q n d T.val :=
                  Submodule.mem_iSup_of_mem (⟨S', hss⟩ : {T : Finset (Fin n) // T ⊂ S}) (hmemD S')
                rw [real_inner_comm]
                exact (Submodule.mem_orthogonal _ _).mp hw.2 _ hmem
              · exact horth S' S hsub w hw.1
          funext x j
          simp only [subsetComponent]
          rw [key]
        rw [hexp ρ]
        funext x j
        simp only [hmain]
