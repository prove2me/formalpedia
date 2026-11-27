-- Prove2me | solution 1 for UniformPrecSched.Makespan.Supplement.theorem_3_11
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:18:20.944108+00:00
-- url     : https://prove2.me/submissions/c0293236-10cf-4159-9ad4-0df906915288

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Supplement_Integral

open UniformPrecSched
open UniformPrecSched.Makespan
open UniformPrecSched.Makespan.Supplement

/-- Chudak–Shmoys, authors' manuscript, p. 10 (proof p. 11), PDF 10–11,
Theorem 3.11. An unbounded family with positive attained integer optima and actual
optimal schedules. The absolute constant is outside every size threshold.
Formalization Note: log is base two; m≥4 keeps log log positive. -/
theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∃ (n m : ℕ) (I : Instance n m)
      (x : Fin (numSpeeds I) → Fin n → ℝ) (C : Fin n → ℝ) (D : ℝ)
      (σ : Schedule I),
      M ≤ m ∧ 4 ≤ m ∧ 0 < n ∧ 0 < D ∧ IPOptimal I x C D ∧
      IsMakespanOptimal I σ ∧
      c * (Real.logb 2 m / Real.logb 2 (Real.logb 2 m)) * D ≤ σ.makespan := by
        classical
        refine ⟨1/6, by norm_num, fun M => ?_⟩
        obtain ⟨a, ha2, haM⟩ : ∃ a : ℕ, 2 ≤ a ∧ M ≤ a := ⟨max M 2, le_max_right _ _, le_max_left _ _⟩
        obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 2 ^ a := ⟨_, rfl⟩
        have hK4 : 4 ≤ K := by
          subst hK
          calc 4 = 2^2 := by norm_num
            _ ≤ 2^a := Nat.pow_le_pow_right (by norm_num) ha2
        have haK : a < K := hK ▸ Nat.lt_two_pow_self
        have hK0 : 0 < K := by omega
        obtain ⟨mc, hmc⟩ : ∃ mc : Fin K → ℕ, ∀ l, mc l = 2 * K ^ (3 * l.val) := ⟨_, fun _ => rfl⟩
        have hmcpos : ∀ l, 0 < mc l := by intro l; rw [hmc]; positivity
        obtain ⟨m, hm, ⟨eM⟩⟩ : ∃ m, m = ∑ l, mc l ∧ Nonempty (Fin m ≃ (Σ l : Fin K, Fin (mc l))) :=
          ⟨_, rfl, ⟨finSigmaFinEquiv.symm⟩⟩
        obtain ⟨n, ⟨eJ⟩⟩ : ∃ n, Nonempty (Fin n ≃ Option (Σ l : Fin K, Fin (K * mc l))) :=
          ⟨_, ⟨(Fintype.equivFin _).symm⟩⟩
        have hr4 : (4:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK4
        have hrpos : (0:ℝ) < K := by linarith
        obtain ⟨I, hs, hp, hprec⟩ : ∃ I : Instance n m,
            (∀ i, I.s i = 1 / (K:ℝ) ^ (eM i).1.val) ∧
            (∀ j, I.p j = (eJ j).elim 1 (fun y => 1 / (2 * (K:ℝ) ^ (y.1.val + 1)))) ∧
            (∀ j j', I.prec j j' ↔ ∃ y y', eJ j = some y ∧ eJ j' = some y' ∧ y.1 < y'.1) := by
          refine ⟨{ p := fun j => (eJ j).elim 1 (fun y => 1 / (2 * (K:ℝ) ^ (y.1.val + 1))),
                    s := fun i => 1 / (K:ℝ) ^ (eM i).1.val,
                    prec := fun j j' => ∃ y y', eJ j = some y ∧ eJ j' = some y' ∧ y.1 < y'.1,
                    m_pos := ?_, p_pos := ?_, s_pos := ?_, prec_irrefl := ?_, prec_trans := ?_ },
                  fun _ => rfl, fun _ => rfl, fun _ _ => Iff.rfl⟩
          · exact Fin.pos (eM.symm ⟨⟨0, hK0⟩, ⟨0, hmcpos _⟩⟩)
          · intro j
            cases eJ j <;> simp <;> positivity
          · intro i; positivity
          · rintro j ⟨y, y', h1, h2, h3⟩
            rw [h1] at h2
            cases h2
            exact lt_irrefl _ h3
          · rintro i j k ⟨x, y, h1, h2, h3⟩ ⟨y', z, h4, h5, h6⟩
            rw [h2] at h4
            cases h4
            exact ⟨x, z, h1, h5, h3.trans h6⟩
        have hpb : ∀ l u, I.p (eJ.symm (some ⟨l, u⟩)) = 1 / (2 * (K:ℝ) ^ (l.val + 1)) := by
          intro l u; rw [hp]; simp
        have hp0 : I.p (eJ.symm none) = 1 := by rw [hp]; simp
        have seq : ∀ (σ : Schedule I) (i : Fin m) (F : ℝ) (A : Finset (Fin n)),
            (∀ j ∈ A, σ.μ j = i) → (∀ j ∈ A, F ≤ σ.S j) →
            A = ∅ ∨ ∃ j ∈ A, F + ∑ j ∈ A, I.p j / I.s i ≤ σ.C j := by
          intro σ i F A
          refine Finset.induction_on_max_value (motive := fun A => (∀ j ∈ A, σ.μ j = i) →
            (∀ j ∈ A, F ≤ σ.S j) → A = ∅ ∨ ∃ j ∈ A, F + ∑ j ∈ A, I.p j / I.s i ≤ σ.C j)
            σ.S A (by simp) ?_
          intro b s hb hmax ih hμ hF
          right
          have hμb : σ.μ b = i := hμ b (Finset.mem_insert_self _ _)
          have hFb : F ≤ σ.S b := hF b (Finset.mem_insert_self _ _)
          have hdb : 0 < I.p b / I.s i := div_pos (I.p_pos b) (I.s_pos i)
          refine ⟨b, Finset.mem_insert_self _ _, ?_⟩
          rw [Finset.sum_insert hb]
          simp only [Schedule.C, hμb]
          rcases ih (fun j hj => hμ j (Finset.mem_insert_of_mem hj))
              (fun j hj => hF j (Finset.mem_insert_of_mem hj)) with h0 | ⟨j, hj, hjle⟩
          · subst h0; simp; linarith
          · have hjb : j ≠ b := fun h => hb (h ▸ hj)
            have hμj : σ.μ j = i := hμ j (Finset.mem_insert_of_mem hj)
            have hov := σ.noOverlap j b hjb (by rw [hμj, hμb])
            simp only [Schedule.C, hμj] at hjle
            rw [hμj, hμb] at hov
            have hSj := hmax j hj
            rcases hov with h | h
            · linarith
            · linarith
        have hsumcls : ∀ g : Fin K → ℕ, ∑ i : Fin m, g (eM i).1 = ∑ l, mc l * g l := by
          intro g
          rw [Equiv.sum_comp eM (fun x => g x.1), Fintype.sum_sigma]
          simp
        have core : ∀ (σ : Schedule I) (k : ℕ) (hk : k < K),
            (∀ u, (k:ℝ) / 2 ≤ σ.S (eJ.symm (some ⟨⟨k, hk⟩, u⟩))) →
            ∃ u, ((k:ℝ) + 1) / 2 ≤ σ.C (eJ.symm (some ⟨⟨k, hk⟩, u⟩)) := by
          intro σ k hk hstart
          by_contra hcon
          push_neg at hcon
          set L : Fin K := ⟨k, hk⟩ with hL
          have hinj : Function.Injective (fun u : Fin (K * mc L) => eJ.symm (some ⟨L, u⟩)) := by
            intro u v h
            simpa using h
          let nI : Fin m → ℕ := fun i =>
            (Finset.univ.filter (fun u : Fin (K * mc L) => σ.μ (eJ.symm (some ⟨L, u⟩)) = i)).card
          have hsum : K * mc L = ∑ i, nI i := by
            have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
              (f := fun u : Fin (K * mc L) => σ.μ (eJ.symm (some ⟨L, u⟩))) (by simp [Set.MapsTo])
            simpa using this
          let h : Fin K → ℕ := fun l => if l.val = k then K - 1 else if l.val < k then K ^ (k + 1 - l.val) else 0
          have hbound : ∀ i, nI i ≤ h (eM i).1 := by
            intro i
            rcases Nat.eq_zero_or_pos (nI i) with h0 | hpos
            · rw [h0]; exact Nat.zero_le _
            set A := (Finset.univ.filter (fun u : Fin (K * mc L) => σ.μ (eJ.symm (some ⟨L, u⟩)) = i)).image
              (fun u : Fin (K * mc L) => eJ.symm (some ⟨L, u⟩)) with hA
            have hAμ : ∀ j ∈ A, σ.μ j = i := by
              intro j hj; rw [hA, Finset.mem_image] at hj
              obtain ⟨u, hu, rfl⟩ := hj
              simpa using hu
            have hAF : ∀ j ∈ A, (k:ℝ)/2 ≤ σ.S j := by
              intro j hj; rw [hA, Finset.mem_image] at hj
              obtain ⟨u, hu, rfl⟩ := hj
              exact hstart u
            have hAsum : ∑ j ∈ A, I.p j / I.s i = (nI i : ℝ) * ((K:ℝ) ^ (eM i).1.val / (2 * (K:ℝ) ^ (k + 1))) := by
              rw [hA, Finset.sum_image (fun u _ v _ h => hinj h)]
              rw [Finset.sum_congr rfl (fun u _ => by rw [hpb, hs])]
              rw [Finset.sum_const, nsmul_eq_mul]
              congr 1
              rw [show L.val = k from rfl]
              field_simp
            rcases seq σ i ((k:ℝ)/2) A hAμ hAF with hA0 | ⟨j, hj, hjle⟩
            · exfalso
              rw [hA, Finset.image_eq_empty] at hA0
              have : nI i = 0 := by simp only [nI]; rw [hA0]; rfl
              omega
            have hjC : σ.C j < ((k:ℝ) + 1) / 2 := by
              rw [hA, Finset.mem_image] at hj
              obtain ⟨u, _, rfl⟩ := hj
              exact hcon u
            rw [hAsum] at hjle
            have hreal : (nI i : ℝ) * (K:ℝ) ^ (eM i).1.val < (K:ℝ) ^ (k + 1) := by
              have h1 : (nI i : ℝ) * ((K:ℝ) ^ (eM i).1.val / (2 * (K:ℝ) ^ (k + 1))) < 1 / 2 := by linarith
              have hpk : (0:ℝ) < (K:ℝ) ^ (k+1) := by positivity
              rw [mul_div_assoc', div_lt_iff₀ (by positivity)] at h1
              linarith
            have hnat : nI i * K ^ (eM i).1.val < K ^ (k + 1) := by exact_mod_cast hreal
            simp only [h]
            set l := (eM i).1.val with hl
            split_ifs with h1 h2
            · rw [h1, pow_succ'] at hnat
              have := Nat.lt_of_mul_lt_mul_right hnat
              omega
            · have : K ^ (k + 1) = K ^ (k + 1 - l) * K ^ l := by rw [← pow_add]; congr 1; omega
              rw [this] at hnat
              exact (Nat.lt_of_mul_lt_mul_right hnat).le
            · have : K ^ (k + 1) ≤ K ^ l := Nat.pow_le_pow_right hK0 (by omega)
              have : nI i * K ^ l < 1 * K ^ l := by omega
              have := Nat.lt_of_mul_lt_mul_right this
              omega
          have hle1 : ∑ i, nI i ≤ ∑ l, mc l * h l := by
            rw [← hsumcls]; exact Finset.sum_le_sum (fun i _ => hbound i)
          have hterm : ∀ l : Fin K, mc l * h l ≤ (if l = L then (K - 1) * mc L else 0) +
              (if l.val < k then 2 * K ^ (3 * k - 1) else 0) := by
            intro l
            simp only [h]
            by_cases h1 : l.val = k
            · have : l = L := Fin.ext h1
              subst this
              have h2 : ¬ (L.val < k) := by omega
              simp [h1, h2, mul_comm]
            · have hne : l ≠ L := fun e => h1 (by rw [e])
              rw [if_neg h1, if_neg hne, zero_add]
              by_cases h2 : l.val < k
              · rw [if_pos h2, if_pos h2, hmc, mul_assoc, ← pow_add]
                exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hK0 (by omega))
              · rw [if_neg h2]; simp
          have hle2 : ∑ l, mc l * h l ≤ (K - 1) * mc L + k * (2 * K ^ (3 * k - 1)) := by
            refine (Finset.sum_le_sum (fun l _ => hterm l)).trans ?_
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ L, if_pos (Finset.mem_univ _)]
            apply Nat.add_le_add_left
            rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then 2 * K ^ (3 * k - 1) else 0) K,
              Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
            have : (Finset.range K).filter (fun i => i < k) = Finset.range k := by
              ext x; simp; omega
            rw [this, Finset.card_range]
          have hfin : (K - 1) * mc L + k * (2 * K ^ (3 * k - 1)) < K * mc L := by
            rw [hmc L]
            simp only [hL]
            rcases Nat.eq_zero_or_pos k with hk0 | hk0
            · subst hk0; simp; omega
            · have e1 : K ^ (3 * k) = K * K ^ (3 * k - 1) := by rw [← pow_succ']; congr 1; omega
              have e2 : K = (K - 1) + 1 := by omega
              rw [e1]
              have : k * (2 * K ^ (3 * k - 1)) < 2 * (K * K ^ (3 * k - 1)) := by
                have hp : 0 < K ^ (3 * k - 1) := by positivity
                nlinarith
              calc (K - 1) * (2 * (K * K ^ (3 * k - 1))) + k * (2 * K ^ (3 * k - 1))
                  < (K - 1) * (2 * (K * K ^ (3 * k - 1))) + 2 * (K * K ^ (3 * k - 1)) := by omega
                _ = ((K - 1) + 1) * (2 * (K * K ^ (3 * k - 1))) := by ring
                _ = K * (2 * (K * K ^ (3 * k - 1))) := by rw [← e2]
          omega
        have blockLB : ∀ (σ : Schedule I) (k : ℕ) (hk : k < K),
            ∃ u, ((k:ℝ) + 1) / 2 ≤ σ.C (eJ.symm (some ⟨⟨k, hk⟩, u⟩)) := by
          intro σ k
          induction k with
          | zero =>
            intro hk
            apply core σ 0 hk
            intro u; simpa using σ.S_nonneg _
          | succ k ih =>
            intro hk
            obtain ⟨u', hu'⟩ := ih (by omega)
            apply core σ (k+1) hk
            intro u
            have hpr : I.prec (eJ.symm (some ⟨⟨k, by omega⟩, u'⟩)) (eJ.symm (some ⟨⟨k+1, hk⟩, u⟩)) :=
              (hprec _ _).2 ⟨⟨⟨k, by omega⟩, u'⟩, ⟨⟨k+1, hk⟩, u⟩, by simp, by simp, by simp [Fin.lt_def]⟩
            have := σ.precedence _ _ hpr
            simp only [Schedule.C] at hu'
            push_cast
            linarith
        have hLB : ∀ σ : Schedule I, (K:ℝ) / 2 ≤ σ.makespan := by
          intro σ
          obtain ⟨u, hu⟩ := blockLB σ (K - 1) (by omega)
          have e : (((K - 1 : ℕ) : ℝ) + 1) = K := by
            rw [Nat.cast_sub (by omega)]; push_cast; ring
          rw [e] at hu
          rw [Schedule.makespan, dif_pos ⟨_, Finset.mem_univ (eJ.symm none)⟩]
          exact hu.trans (Finset.le_sup' σ.C (Finset.mem_univ _))
        have hdiv : ∀ l : ℕ, (1 / (2 * (K:ℝ) ^ (l + 1))) / (1 / (K:ℝ) ^ l) = 1 / (2 * K) := by
          intro l; field_simp; ring
        have hdivK : ∀ x : (Σ l : Fin K, Fin (K * mc l)), x.2.val / K < mc x.1 := by
          intro x
          rw [Nat.div_lt_iff_lt_mul hK0]; simpa [Nat.mul_comm] using x.2.isLt
        obtain ⟨σ, hσ⟩ : ∃ σ : Schedule I, σ.makespan ≤ (K:ℝ) / 2 := by
          let μ : Fin n → Fin m := fun j => (eJ j).elim (eM.symm ⟨⟨0, hK0⟩, ⟨0, hmcpos _⟩⟩)
            (fun x => eM.symm ⟨x.1, ⟨x.2.val / K, hdivK x⟩⟩)
          let S : Fin n → ℝ := fun j => (eJ j).elim (1/2)
            (fun x => (x.1.val : ℝ) / 2 + ((x.2.val % K : ℕ) : ℝ) / (2 * K))
          have hdur : ∀ j, I.p j / I.s (μ j) = (eJ j).elim 1 (fun _ => 1 / (2 * (K:ℝ))) := by
            intro j
            rw [hp]
            cases h : eJ j with
            | none => simp [μ, h, hs]
            | some x => simp only [μ, h, Option.elim_some, Option.elim, hs, Equiv.apply_symm_apply]; exact hdiv _
          have hmod : ∀ x : (Σ l : Fin K, Fin (K * mc l)), ((x.2.val % K : ℕ) : ℝ) + 1 ≤ K := by
            intro x
            have : x.2.val % K + 1 ≤ K := Nat.mod_lt _ hK0
            exact_mod_cast this
          have hC : ∀ x : (Σ l : Fin K, Fin (K * mc l)),
              (x.1.val : ℝ) / 2 + ((x.2.val % K : ℕ) : ℝ) / (2 * K) + 1 / (2 * K) ≤ ((x.1.val:ℝ) + 1) / 2 := by
            intro x
            have := hmod x
            have e : ((x.2.val % K : ℕ) : ℝ) / (2 * K) + 1 / (2 * K) = (((x.2.val % K : ℕ) : ℝ) + 1) / (2 * K) := by
              ring
            rw [add_assoc, e]
            have : (((x.2.val % K : ℕ) : ℝ) + 1) / (2 * K) ≤ 1 / 2 := by
              rw [div_le_iff₀ (by positivity)]; linarith
            linarith
          refine ⟨{ μ := μ, S := S, S_nonneg := ?_, noOverlap := ?_, precedence := ?_ }, ?_⟩
          · intro j
            cases h : eJ j with
            | none => simp [S, h]
            | some x => simp only [S, h, Option.elim_some, Option.elim]; positivity
          · intro i j hij hμ
            rw [hdur i, hdur j]
            cases hi : eJ i with
            | none =>
              cases hj : eJ j with
              | none => exact absurd (eJ.injective (hi.trans hj.symm)) hij
              | some y =>
                simp only [μ, hi, hj, Option.elim] at hμ
                have hμ' := congrArg eM hμ
                simp only [Equiv.apply_symm_apply] at hμ'
                have h0 := congrArg (fun z => z.1.val) hμ'
                simp only at h0
                right
                simp only [S, hi, hj, Option.elim]
                have := hC y
                have hy0 : (y.1.val:ℝ) = 0 := by exact_mod_cast h0.symm
                rw [hy0] at this ⊢
                norm_num at this ⊢
                linarith
            | some x =>
              cases hj : eJ j with
              | none =>
                simp only [μ, hi, hj, Option.elim] at hμ
                have hμ' := congrArg eM hμ
                simp only [Equiv.apply_symm_apply] at hμ'
                have h0 := congrArg (fun z => z.1.val) hμ'
                simp only at h0
                left
                simp only [S, hi, hj, Option.elim]
                have := hC x
                have hx0 : (x.1.val:ℝ) = 0 := by exact_mod_cast h0
                rw [hx0] at this ⊢
                norm_num at this ⊢
                linarith
              | some y =>
                simp only [μ, hi, hj, Option.elim] at hμ
                have hμ' := congrArg eM hμ
                simp only [Equiv.apply_symm_apply] at hμ'
                have h1 := congrArg (fun z => z.1.val) hμ'
                have h2 := congrArg (fun z => z.2.val) hμ'
                simp only at h1 h2
                simp only [S, hi, hj, Option.elim]
                have hne : x.2.val % K ≠ y.2.val % K := by
                  intro hm
                  apply hij
                  apply eJ.injective
                  rw [hi, hj]
                  obtain ⟨x1, x2⟩ := x
                  obtain ⟨y1, y2⟩ := y
                  simp only at h1 h2 hm
                  have e1 : x1 = y1 := Fin.ext h1
                  subst e1
                  have e2 : x2 = y2 := by
                    apply Fin.ext
                    rw [← Nat.div_add_mod x2.val K, ← Nat.div_add_mod y2.val K, h2, hm]
                  rw [e2]
                have h1' : (x.1.val : ℝ) = y.1.val := by exact_mod_cast h1
                rcases lt_or_gt_of_ne hne with hlt | hlt
                · left
                  have : ((x.2.val % K : ℕ) : ℝ) + 1 ≤ ((y.2.val % K : ℕ) : ℝ) := by exact_mod_cast hlt
                  rw [h1']
                  have e : ((x.2.val % K : ℕ) : ℝ) / (2 * K) + 1 / (2 * K) = (((x.2.val % K : ℕ) : ℝ) + 1) / (2 * K) := by ring
                  rw [add_assoc, e]
                  gcongr
                · right
                  have : ((y.2.val % K : ℕ) : ℝ) + 1 ≤ ((x.2.val % K : ℕ) : ℝ) := by exact_mod_cast hlt
                  rw [h1']
                  have e : ((y.2.val % K : ℕ) : ℝ) / (2 * K) + 1 / (2 * K) = (((y.2.val % K : ℕ) : ℝ) + 1) / (2 * K) := by ring
                  rw [add_assoc, e]
                  gcongr
          · intro i j hij
            obtain ⟨x, y, hx, hy, hxy⟩ := (hprec i j).1 hij
            show S i + I.p i / I.s (μ i) ≤ S j
            rw [hdur i]
            simp only [S, hx, hy, Option.elim]
            have := hC x
            have h2 : (x.1.val : ℝ) + 1 ≤ y.1.val := by exact_mod_cast hxy
            have : (0:ℝ) ≤ ((y.2.val % K : ℕ) : ℝ) / (2 * K) := by positivity
            linarith
          · rw [Schedule.makespan, dif_pos ⟨_, Finset.mem_univ (eJ.symm none)⟩]
            apply Finset.sup'_le
            intro j _
            show S j + I.p j / I.s (μ j) ≤ (K:ℝ) / 2
            rw [hdur j]
            cases h : eJ j with
            | none => simp only [S, h, Option.elim]; linarith
            | some x =>
              simp only [S, h, Option.elim]
              have := hC x
              have : (x.1.val : ℝ) + 1 ≤ K := by exact_mod_cast x.1.isLt
              linarith
        -- class speeds
        have hcsinj : Function.Injective (classSpeed I) := by
          intro u v huv
          unfold classSpeed at huv
          exact Fin.rev_injective ((Finset.orderEmbOfFin _ _).injective huv)
        have hcsmem : ∀ κ, ∃ i, I.s i = classSpeed I κ := by
          intro κ
          have := Finset.orderEmbOfFin_mem (speedSet I) (rfl : (speedSet I).card = numSpeeds I) (Fin.rev κ)
          obtain ⟨i, _, hi⟩ := Finset.mem_image.1 (this : _ ∈ Finset.univ.image I.s)
          exact ⟨i, hi⟩
        have hcssurj : ∀ i, ∃ κ, classSpeed I κ = I.s i := by
          intro i
          have hmem : I.s i ∈ (Set.range ((speedSet I).orderEmbOfFin (rfl : (speedSet I).card = numSpeeds I))) := by
            rw [Finset.range_orderEmbOfFin]; simp [speedSet]
          obtain ⟨t, ht⟩ := hmem
          refine ⟨Fin.rev (t : Fin (numSpeeds I)), ?_⟩
          unfold classSpeed
          convert ht using 2
          exact Fin.rev_rev _
        have hpowinj : ∀ u v : ℕ, (1:ℝ) / (K:ℝ) ^ u = 1 / (K:ℝ) ^ v → u = v := by
          intro u v h
          rw [one_div, one_div, inv_inj] at h
          have h' : K ^ u = K ^ v := by exact_mod_cast h
          exact Nat.pow_right_injective (by omega) h'
        -- the class of a job
        have hcl : ∀ l : Fin K, ∃ κ, classSpeed I κ = 1 / (K:ℝ) ^ l.val := by
          intro l
          obtain ⟨κ, hκ⟩ := hcssurj (eM.symm ⟨l, ⟨0, hmcpos l⟩⟩)
          exact ⟨κ, by rw [hκ, hs]; simp⟩
        have hcsl : ∀ κ, ∃ l : Fin K, classSpeed I κ = 1 / (K:ℝ) ^ l.val := by
          intro κ
          obtain ⟨i, hi⟩ := hcsmem κ
          exact ⟨(eM i).1, by rw [← hi, hs]⟩
        have hcount : ∀ κ (l : Fin K), classSpeed I κ = 1 / (K:ℝ) ^ l.val → (classCount I κ : ℝ) = mc l := by
          intro κ l hκ
          unfold classCount
          rw [hκ]
          have : (Finset.univ.filter fun i => I.s i = 1 / (K:ℝ) ^ l.val) =
              Finset.univ.filter fun i => (eM i).1 = l := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs]
            constructor
            · intro h; exact Fin.ext (hpowinj _ _ h)
            · intro h; rw [h]
          rw [this, Finset.card_filter]
          have := hsumcls (fun l' => if l' = l then 1 else 0)
          beta_reduce at this
          rw [this]
          simp
        obtain ⟨cl, hcl0, hcl1⟩ : ∃ cl : Fin n → Fin K, cl (eJ.symm none) = ⟨0, hK0⟩ ∧
            ∀ l u, cl (eJ.symm (some ⟨l, u⟩)) = l :=
          ⟨fun j => (eJ j).elim ⟨0, hK0⟩ (fun y => y.1), by simp, by simp⟩
        obtain ⟨x, hx⟩ : ∃ x : Fin (numSpeeds I) → Fin n → ℝ, ∀ κ j,
            x κ j = if classSpeed I κ = 1 / (K:ℝ) ^ (cl j).val then 1 else 0 := ⟨_, fun _ _ => rfl⟩
        obtain ⟨C, hC0, hC1⟩ : ∃ C : Fin n → ℝ, C (eJ.symm none) = 1 ∧
            ∀ l u, C (eJ.symm (some ⟨l, u⟩)) = ((l.val:ℝ) + 1) / (2 * K) :=
          ⟨fun j => (eJ j).elim 1 (fun y => ((y.1.val:ℝ) + 1) / (2 * K)), by simp, by simp⟩
        -- x as indicator of a unique class
        have hxind : ∀ j, ∃ κ0, classSpeed I κ0 = 1 / (K:ℝ) ^ (cl j).val ∧
            ∀ κ, x κ j = if κ = κ0 then 1 else 0 := by
          intro j
          obtain ⟨κ0, h0⟩ := hcl (cl j)
          refine ⟨κ0, h0, fun κ => ?_⟩
          rw [hx]
          congr 1
          apply propext
          constructor
          · intro h; exact hcsinj (h.trans h0.symm)
          · intro h; rw [h, h0]
        have hsumx : ∀ j (f : Fin (numSpeeds I) → ℝ), ∃ κ0, classSpeed I κ0 = 1 / (K:ℝ) ^ (cl j).val ∧
            ∑ κ, f κ * x κ j = f κ0 := by
          intro j f
          obtain ⟨κ0, h0, h1⟩ := hxind j
          exact ⟨κ0, h0, by simp [h1]⟩
        -- every job is either the dummy or a block job
        have hjcases : ∀ j, j = eJ.symm none ∨ ∃ l u, j = eJ.symm (some ⟨l, u⟩) := by
          intro j
          cases h : eJ j with
          | none => left; rw [← h]; simp
          | some y => right; exact ⟨y.1, y.2, by rw [← h]; simp⟩
        have hpj : ∀ j, I.p j / (1 / (K:ℝ) ^ (cl j).val) ≤ C j ∧ I.p j / (1 / (K:ℝ) ^ (cl j).val) = (eJ j).elim 1 (fun _ => 1 / (2 * (K:ℝ))) := by
          intro j
          rcases hjcases j with rfl | ⟨l, u, rfl⟩
          · rw [hp0, hcl0, hC0]; simp
          · rw [hpb, hcl1, hC1, hdiv]
            simp only [Equiv.apply_symm_apply, Option.elim]
            refine ⟨?_, trivial⟩
            gcongr
            linarith [(Nat.cast_nonneg l.val : (0:ℝ) ≤ l.val)]
        have hIPfeas : IPFeasible I x C 1 := by
          refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · intro j
            obtain ⟨κ0, _, h⟩ := hsumx j (fun _ => 1)
            simpa using h
          · intro κ
            obtain ⟨l, hl⟩ := hcsl κ
            rw [hcount κ l hl, hl]
            have hW : ∑ j, I.p j * x κ j = (if l.val = 0 then 1 else 0) + (K * mc l : ℕ) * (1 / (2 * (K:ℝ) ^ (l.val + 1))) := by
              have hxκ : ∀ j, x κ j = if cl j = l then 1 else 0 := by
                intro j; rw [hx, hl]
                congr 1; apply propext
                constructor
                · intro h; exact Fin.ext (hpowinj _ _ h).symm
                · intro h; rw [h]
              simp_rw [hxκ]
              rw [← Equiv.sum_comp eJ.symm, Fintype.sum_option, Fintype.sum_sigma]
              rw [hp0, hcl0]
              simp only [hpb, hcl1]
              have : ((⟨0, hK0⟩ : Fin K) = l) ↔ l.val = 0 := by
                constructor
                · intro h; rw [← h]
                · intro h; exact Fin.ext h.symm
              simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_const, Finset.card_univ,
                Fintype.card_fin, nsmul_eq_mul]
              congr 1
              rw [Finset.sum_ite_eq']
              simp
            rw [hW, hmc l]
            push_cast
            have hKl : (0:ℝ) < (K:ℝ) ^ l.val := by positivity
            split_ifs with h0
            · rw [h0]; norm_num; field_simp; norm_num
            · field_simp
              rw [pow_succ]
              have : 0 < (K:ℝ)^l.val * (K:ℝ)^(3*l.val) * K := by positivity
              nlinarith
          · intro j
            obtain ⟨κ0, h0, h⟩ := hsumx j (fun κ => I.p j / classSpeed I κ)
            rw [h, h0]; exact (hpj j).1
          · intro j' j hpr
            obtain ⟨y', y, hy', hy, hlt⟩ := (hprec j' j).1 hpr
            obtain ⟨κ0, h0, h⟩ := hsumx j (fun κ => I.p j / classSpeed I κ)
            rw [h, h0, (hpj j).2, hy]
            have e1 : j = eJ.symm (some y) := by rw [← hy]; simp
            have e2 : j' = eJ.symm (some y') := by rw [← hy']; simp
            rw [e1, e2, hC1, hC1]
            simp only [Option.elim]
            have : (y'.1.val : ℝ) + 1 ≤ y.1.val := by exact_mod_cast hlt
            rw [div_sub_div_same, div_le_div_iff_of_pos_right (by positivity)]
            linarith
          · intro j
            rcases hjcases j with rfl | ⟨l, u, rfl⟩
            · rw [hC0]
            · rw [hC1, div_le_one (by positivity)]
              have : (l.val : ℝ) + 1 ≤ K := by exact_mod_cast l.isLt
              linarith
          · intro κ j; rw [hx]; split_ifs <;> norm_num
          · intro κ j; rw [hx]; split_ifs <;> simp
        have hIPopt : IPOptimal I x C 1 := by
          refine ⟨hIPfeas, fun x' C' D' hf => ?_⟩
          obtain ⟨⟨h1, _, h3, _, h5, h6⟩, _⟩ := hf
          have hle : ∑ κ, x' κ (eJ.symm none) ≤ ∑ κ, I.p (eJ.symm none) / classSpeed I κ * x' κ (eJ.symm none) := by
            apply Finset.sum_le_sum
            intro κ _
            obtain ⟨l, hl⟩ := hcsl κ
            rw [hp0, hl, one_div_one_div]
            have : (1:ℝ) ≤ (K:ℝ) ^ l.val := one_le_pow₀ (by linarith)
            nlinarith [h6 κ (eJ.symm none)]
          have := h3 (eJ.symm none)
          have := h5 (eJ.symm none)
          rw [h1] at hle
          linarith
        have hmlo : 2 ^ K ≤ m := by
          have h1 : mc ⟨K - 1, by omega⟩ ≤ m := by
            rw [hm]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
          rw [hmc] at h1
          simp only at h1
          calc 2 ^ K ≤ 2 ^ (3 * (K - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ ≤ K ^ (3 * (K - 1)) := Nat.pow_le_pow_left (by omega) _
            _ ≤ 2 * K ^ (3 * (K - 1)) := by omega
            _ ≤ m := h1
        have hmhi : m ≤ 2 ^ (3 * a * K) := by
          have h1 : m ≤ K * (2 * K ^ (3 * (K - 1))) := by
            rw [hm]
            have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin K)) mc (2 * K ^ (3 * (K - 1)))
              (fun l _ => by rw [hmc]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hK0 (by omega)))
            simpa using this
          have h2 : 2 ^ (3 * a * K) = K ^ (3 * (K - 1)) * (K * K * K) := by
            have e1 : (2:ℕ) ^ (3 * a * K) = (2 ^ a) ^ (3 * K) := by
              rw [← pow_mul]; congr 1; ring
            rw [e1, ← hK, show 3 * K = 3 * (K - 1) + 3 by omega, pow_add]
            ring
          rw [h2]
          have hp : 0 < K ^ (3 * (K - 1)) := by positivity
          calc m ≤ K * (2 * K ^ (3 * (K - 1))) := h1
            _ = K ^ (3 * (K - 1)) * (2 * K) := by ring
            _ ≤ K ^ (3 * (K - 1)) * (K * K * K) := Nat.mul_le_mul_left _ (by nlinarith)
        have hmR1 : (2:ℝ) ^ K ≤ m := by exact_mod_cast hmlo
        have hmR2 : (m:ℝ) ≤ 2 ^ (3 * a * K) := by exact_mod_cast hmhi
        have hL1 : Real.logb 2 m ≤ 3 * a * K := by
          have := Real.logb_le_logb_of_le (b := 2) (by norm_num)
            (by have : (0:ℝ) < 2 ^ K := by positivity
                linarith) hmR2
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
          push_cast at this; linarith
        have hL2 : (K:ℝ) ≤ Real.logb 2 m := by
          have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hmR1
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
          linarith
        have hLL : (a:ℝ) ≤ Real.logb 2 (Real.logb 2 m) := by
          have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hrpos hL2
          have e : (K:ℝ) = 2 ^ a := by rw [hK]; push_cast; ring
          rw [e, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
          linarith
        have ha0 : (0:ℝ) < a := by have : 2 ≤ a := ha2; positivity
        have hratio : Real.logb 2 m / Real.logb 2 (Real.logb 2 m) ≤ 3 * K := by
          rw [div_le_iff₀ (by linarith)]
          have hK0' : (0:ℝ) ≤ K := by positivity
          nlinarith
        refine ⟨n, m, I, x, C, 1, σ, ?_, ?_, Fin.pos (eJ.symm none), one_pos, hIPopt,
          fun σ' => hσ.trans (hLB σ'), ?_⟩
        · have : K ≤ 2 ^ K := Nat.lt_two_pow_self.le
          omega
        · have : K ≤ 2 ^ K := Nat.lt_two_pow_self.le
          omega
        · have := hLB σ
          nlinarith
