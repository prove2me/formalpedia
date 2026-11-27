-- Prove2me | solution 1 for ProcureAssort.Hotelling.Supplement.theorem_G_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:42:31.468701+00:00
-- url     : https://prove2.me/submissions/2738273f-ac33-4ef1-827b-bf8f8c3383ba

import Definitions.Def_ProcureAssort_Hotelling_Supplement_Affine

open ProcureAssort
open ProcureAssort.Hotelling
open ProcureAssort.Hotelling.Supplement

theorem solution (n : ℕ) (hn : 0 < n) (M : QuadraticMarket (Fin n))
    (hM : M.Valid) (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (hTypes : ValidTypes Θ f) (hReg : Regular Θ f) (hRIOM : RIOM Θ (affQ M Θ f)) :
    optDecLin Θ f M.gcs (simplex n) = optCent Θ f M.gcs (simplex n) ∧
      ValuesWellDefined Θ f M.gcs := by
        have A1 (n : ℕ) (hn : 0 < n) (M : QuadraticMarket (Fin n)) :
           ∀ p : Fin n → ℝ, M.demand Finset.univ p ∈ simplex n ∧
              ∀ y ∈ simplex n, CS M.gcs y p ≤ CS M.gcs (M.demand Finset.univ p) p := by
          intro p
          have hex : ∃ x, M.IsDemand Finset.univ p x := by
            have hc : IsCompact (stdSimplex ℝ (Fin n)) := isCompact_stdSimplex ℝ (Fin n)
            have hne : (stdSimplex ℝ (Fin n)).Nonempty :=
              ⟨_, single_mem_stdSimplex ℝ (⟨0, hn⟩ : Fin n)⟩
            have hcont : Continuous (fun x : Fin n → ℝ => M.gcs x - ∑ i, p i * x i) := by
              unfold QuadraticMarket.gcs
              fun_prop
            obtain ⟨x, hx, hmax⟩ := hc.exists_isMaxOn hne hcont.continuousOn
            refine ⟨x, hx, by simp, ?_⟩
            intro y hy _
            exact hmax hy
          have h := Classical.epsilon_spec hex
          refine ⟨h.1, ?_⟩
          intro y hy
          exact h.2.2 y hy (by simp)
        have A2 (n : ℕ) (M : QuadraticMarket (Fin n)) (hM : M.Valid) :
           ∀ p x : Fin n → ℝ, x ∈ simplex n → (∀ y ∈ simplex n, CS M.gcs y p ≤ CS M.gcs x p) →
            (∀ i, 0 < x i) → ∃ lam : ℝ, ∀ i, ∑ j, M.D i j * x j = M.c i - p i - lam := by
          intro p x hx hopt hpos
          have hDs : ∀ i j, M.D i j = M.D j i := by
            have h1 : M.gamma.IsHermitian := hM.2.1.1
            have h2 : (M.gamma⁻¹).IsHermitian := h1.inv
            intro i j
            have := h2.apply j i
            simpa [QuadraticMarket.D] using this
          have quad : ∀ (al be ep : ℝ), 0 < ep → (∀ t, |t| ≤ ep → al * t - be * t^2 ≤ 0) → al = 0 := by
            intro al be ep hep h
            by_contra hal
            have hb : 0 < |be| + 1 := by positivity
            have hapos : 0 < |al| := abs_pos.mpr hal
            set s := min ep (|al| / (2 * (|be| + 1))) with hs
            have hs0 : 0 < s := lt_min hep (by positivity)
            have hs1 : s ≤ ep := min_le_left _ _
            have hs2 : s * (2 * (|be| + 1)) ≤ |al| := by
              have : s ≤ |al| / (2 * (|be| + 1)) := min_le_right _ _
              rwa [le_div_iff₀ (by positivity)] at this
            have hbe : be * s ≤ |be| * s := mul_le_mul_of_nonneg_right (le_abs_self _) hs0.le
            rcases le_total 0 al with h0 | h0
            · have := h s (by rw [abs_of_pos hs0]; exact hs1)
              rw [abs_of_nonneg h0] at *
              nlinarith
            · have := h (-s) (by rw [abs_neg, abs_of_pos hs0]; exact hs1)
              rw [abs_of_nonpos h0] at *
              nlinarith
          have key : ∀ i k, (M.c i - p i - ∑ j, M.D i j * x j) = (M.c k - p k - ∑ j, M.D k j * x j) := by
            intro i k
            by_cases hik : i = k
            · rw [hik]
            set u : Fin n → ℝ := Pi.single i 1 - Pi.single k 1 with hu
            have hsumu : ∀ w : Fin n → ℝ, ∑ j, w j * u j = w i - w k := by
              intro w
              simp [hu, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
            have hui : u i = 1 := by simp [hu, Pi.single_apply, hik]
            have huk : u k = -1 := by simp [hu, Pi.single_apply, Ne.symm hik]
            have huo : ∀ j, j ≠ i → j ≠ k → u j = 0 := by
              intro j h1 h2; simp [hu, Pi.single_apply, h1, h2]
            have := quad ((M.c i - p i - ∑ j, M.D i j * x j) - (M.c k - p k - ∑ j, M.D k j * x j))
              ((∑ a, ∑ b, u a * M.D a b * u b) / 2) (min (x i) (x k)) (lt_min (hpos i) (hpos k)) ?_
            · linarith
            intro t ht
            have ht1 := (abs_le.mp (le_trans ht (min_le_left _ _)))
            have ht2 := (abs_le.mp (le_trans ht (min_le_right _ _)))
            have hy : (fun j => x j + t * u j) ∈ simplex n := by
              constructor
              · intro j
                by_cases h1 : j = i
                · subst h1; simp only [hui]; linarith
                · by_cases h2 : j = k
                  · subst h2; simp only [huk]; linarith
                  · simp only [huo j h1 h2]; linarith [hpos j]
              · rw [Finset.sum_add_distrib, hx.2, ← Finset.mul_sum]
                have := hsumu (fun _ => 1)
                simp at this
                rw [this]; ring
            have h := hopt _ hy
            unfold CS QuadraticMarket.gcs at h
            have e1 : ∑ j, M.c j * (x j + t * u j) = ∑ j, M.c j * x j + t * (M.c i - M.c k) := by
              rw [← hsumu M.c, Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl (fun _ _ => by ring)
            have e2 : ∑ j, p j * (x j + t * u j) = ∑ j, p j * x j + t * (p i - p k) := by
              rw [← hsumu p, Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl (fun _ _ => by ring)
            have e4 : ∑ a, ∑ b, u a * M.D a b * x b = ∑ j, M.D i j * x j - ∑ j, M.D k j * x j := by
              rw [← hsumu (fun a => ∑ j, M.D a j * x j)]
              refine Finset.sum_congr rfl (fun a _ => ?_)
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl (fun _ _ => by ring)
            have e5 : ∑ a, ∑ b, x a * M.D a b * u b = ∑ j, M.D i j * x j - ∑ j, M.D k j * x j := by
              rw [← e4, Finset.sum_comm]
              refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
              rw [hDs b a]; ring
            have e3 : ∑ a, ∑ b, (x a + t * u a) * M.D a b * (x b + t * u b) =
                ∑ a, ∑ b, x a * M.D a b * x b + t * (∑ a, ∑ b, u a * M.D a b * x b)
                 + t * (∑ a, ∑ b, x a * M.D a b * u b) + t^2 * (∑ a, ∑ b, u a * M.D a b * u b) := by
              simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
            simp only [] at h
            rw [e1, e2, e3, e4, e5] at h
            nlinarith
          by_cases hne : Nonempty (Fin n)
          · obtain ⟨i0⟩ := hne
            refine ⟨M.c i0 - p i0 - ∑ j, M.D i0 j * x j, fun i => ?_⟩
            linarith [key i i0]
          · exact ⟨0, fun i => (hne ⟨i⟩).elim⟩
        have A3 (n : ℕ) (hn : 0 < n) (M : QuadraticMarket (Fin n)) (hM : M.Valid) 
          (A2 : ∀ p x : Fin n → ℝ, x ∈ simplex n → (∀ y ∈ simplex n, CS M.gcs y p ≤ CS M.gcs x p) →
            (∀ i, 0 < x i) → ∃ lam : ℝ, ∀ i, ∑ j, M.D i j * x j = M.c i - p i - lam) :
           ∃ (d : Fin n → ℝ) (A : Fin n → Fin n → ℝ), (∀ i j, A i j = A j i) ∧
             (∀ z : Fin n → ℝ, (∀ i, ∑ j, A i j * z j = 0) → ∀ i j, z i = z j) ∧
             (∀ i, ∑ j, A i j = 0) ∧
             (∀ i, (∃ j, j ≠ i) → A i i ≠ 0) ∧
            ∀ p x : Fin n → ℝ, x ∈ simplex n → (∀ y ∈ simplex n, CS M.gcs y p ≤ CS M.gcs x p) →
            (∀ i, 0 < x i) → ∀ i, x i = d i + ∑ j, A i j * p j := by
          have hPD := hM.2.1
          have hGs : ∀ i j, M.gamma i j = M.gamma j i := by
            intro i j
            have := hPD.1.apply j i
            simpa using this
          have hpd : ∀ z : Fin n → ℝ, z ≠ 0 → 0 < ∑ i, z i * ∑ j, M.gamma i j * z j := by
            intro z hz
            have := hPD.dotProduct_mulVec_pos hz
            simpa [dotProduct, Matrix.mulVec] using this
          have hunit : IsUnit M.gamma.det := (Matrix.isUnit_iff_isUnit_det _).mp hPD.isUnit
          have hGD : M.gamma * M.D = 1 := Matrix.mul_nonsing_inv _ hunit
          set r : Fin n → ℝ := fun i => ∑ j, M.gamma i j with hr
          set s : ℝ := ∑ i, r i with hs
          have hone : (fun _ : Fin n => (1:ℝ)) ≠ 0 := by
            intro h; have := congrFun h ⟨0, hn⟩; simp at this
          have hspos : 0 < s := by
            have := hpd _ hone
            simpa [hs, hr] using this
          have hcol : ∀ (w : Fin n → ℝ), ∑ i, ∑ j, M.gamma i j * w j = ∑ j, r j * w j := by
            intro w
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [hr, Finset.sum_mul]
            exact Finset.sum_congr rfl (fun i _ => by rw [hGs])
          have hA : ∀ (z : Fin n → ℝ) i, ∑ j, (-M.gamma i j + r i * r j / s) * z j =
              -(∑ j, M.gamma i j * z j) + r i * (∑ j, r j * z j) / s := by
            intro z i
            simp only [add_mul, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
            congr 1
            rw [Finset.mul_sum, Finset.sum_div]
            exact Finset.sum_congr rfl (fun j _ => by ring)
          refine ⟨fun i => (∑ j, M.gamma i j * M.c j) - r i * ((∑ j, r j * M.c j) - 1) / s,
            fun i j => -M.gamma i j + r i * r j / s, ?_, ?_, ?_, ?_, ?_⟩
          · intro i j
            simp only [hGs i j]; ring
          · intro z hz
            simp only [hA] at hz
            set k := (∑ j, r j * z j) / s with hk
            have hzero : (fun i => z i - k) = 0 := by
              by_contra hne
              have h1 := hpd _ hne
              have h2 : ∀ i, ∑ j, M.gamma i j * (z j - k) = 0 := by
                intro i
                have := hz i
                simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
                have h3 : r i * (∑ j, r j * z j) / s = r i * k := by rw [hk]; ring
                rw [h3] at this
                change _ - r i * k = 0
                linarith
              simp [h2] at h1
            intro i j
            have h1 := congrFun hzero i
            have h2 := congrFun hzero j
            simp at h1 h2
            linarith
          · intro i
            have := hA (fun _ => 1) i
            simp only [mul_one] at this
            rw [this]
            change -(r i) + r i * s / s = 0
            field_simp
            ring
          · rintro i ⟨j, hj⟩ h0
            simp only at h0
            have hgii : 0 < M.gamma i i := by
              have hne : (Pi.single i 1 : Fin n → ℝ) ≠ 0 := by
                intro h; have := congrFun h i; simp at this
              have := hpd _ hne
              simpa [Pi.single_apply] using this
            set z : Fin n → ℝ := fun k => 1 - (r i / M.gamma i i) * (Pi.single i 1 : Fin n → ℝ) k with hz
            have hzne : z ≠ 0 := by
              intro h; have := congrFun h j
              simp [hz, Pi.single_apply, hj] at this
            have h1 := hpd z hzne
            have h2 : ∀ a, ∑ b, M.gamma a b * z b = r a - (r i / M.gamma i i) * M.gamma a i := by
              intro a
              simp [hz, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, hr]
              ring
            simp only [h2] at h1
            have h3 : ∑ a, z a * (r a - (r i / M.gamma i i) * M.gamma a i) =
               ∑ a, (r a - (r i / M.gamma i i) * M.gamma a i) - (r i / M.gamma i i) * (r i - (r i / M.gamma i i) * M.gamma i i) := by
              simp [hz, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
            rw [h3, Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
            have h4 : ∑ a, M.gamma a i = r i := by
              rw [hr]; exact Finset.sum_congr rfl (fun a _ => hGs a i)
            rw [h4] at h1
            change 0 < s - _ - _ at h1
            have h5 : r i / M.gamma i i * M.gamma i i = r i := by field_simp
            rw [h5] at h1
            have h6 : r i * r i = M.gamma i i * s := by
              field_simp at h0
              linarith
            have h7 : r i / M.gamma i i * r i = s := by
              rw [div_mul_eq_mul_div, h6]; field_simp
            rw [h7] at h1
            simp at h1
          · intro p x hx hopt hpos i
            obtain ⟨lam, hlam⟩ := A2 p x hx hopt hpos
            have hxeq : ∀ i, x i = (∑ j, M.gamma i j * (M.c j - p j)) - lam * r i := by
              intro i
              have h1 : M.gamma.mulVec (M.D.mulVec x) = x := by
                rw [Matrix.mulVec_mulVec, hGD, Matrix.one_mulVec]
              have h2 : M.D.mulVec x = fun i => M.c i - p i - lam := by
                funext i; rw [← hlam i]; rfl
              rw [h2] at h1
              have h3 := congrFun h1 i
              rw [← h3]
              simp only [Matrix.mulVec, dotProduct, hr, Finset.mul_sum, ← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl (fun _ _ => by ring)
            have hsum : 1 = (∑ j, r j * (M.c j - p j)) - lam * s := by
              rw [← hx.2, ← hcol]
              simp only [hxeq, Finset.sum_sub_distrib, hs, Finset.mul_sum]
            have hl : lam = ((∑ j, r j * (M.c j - p j)) - 1) / s := by
              rw [eq_div_iff hspos.ne']; linarith
            rw [hxeq i, hA, hl]
            simp only [mul_sub, Finset.sum_sub_distrib]
            ring
        have D1 : ∀ (K L : Type) [Fintype K] [Fintype L] (W : K → L → ℝ) (m : K → ℝ),
           (∀ y : K → ℝ, (∀ l, ∑ k, y k * W k l = 0) → ∑ k, y k * m k = 0) →
            ∃ lam : L → ℝ, ∀ k, ∑ l, W k l * lam l = m k := by
          classical
          intro K L _ _ W m h
          set Φ : (L → ℝ) →ₗ[ℝ] (K → ℝ) := Matrix.mulVecLin (Matrix.of W) with hΦ
          by_cases hm : m ∈ LinearMap.range Φ
          · obtain ⟨lam, hl⟩ := hm
            refine ⟨lam, fun k => ?_⟩
            rw [← hl]
            simp [hΦ, Matrix.mulVec, dotProduct]
          · exfalso
            obtain ⟨φ, hφ, hker⟩ := Submodule.exists_le_ker_of_notMem hm
            have hrep : ∀ w : K → ℝ, φ w = ∑ k, φ (Pi.single k 1) * w k := by
              intro w
              have hw : w = ∑ k, w k • (Pi.single k 1 : K → ℝ) := by
                funext j
                simp [Finset.sum_apply, Pi.single_apply]
              conv_lhs => rw [hw]
              rw [map_sum]
              refine Finset.sum_congr rfl (fun k _ => ?_)
              rw [map_smul, smul_eq_mul, mul_comm]
            apply hφ
            rw [hrep]
            apply h
            intro l
            have h1 : Φ (Pi.single l 1) ∈ LinearMap.ker φ := hker ⟨_, rfl⟩
            rw [LinearMap.mem_ker, hrep] at h1
            rw [← h1]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            simp [hΦ]
        have B1 (n : ℕ) (Θ : Fin n → Finset ℝ) (B : Fin n → Finset ℝ)
          (hBs : ∀ i, B i ⊆ Θ i) (hB3 : ∀ i, 3 ≤ (B i).card)
          (v : Fin n → ℝ → ℝ) (hv : ∀ i, ∀ a ∈ Θ i, ∀ b ∈ Θ i, v i a = v i b → a = b)
          (x : Profile Θ → Fin n → ℝ) (hx1 : ∀ θ, ∑ i, x θ i = 1)
          (d : Fin n → ℝ) (A : Fin n → Fin n → ℝ) (hAs : ∀ i j, A i j = A j i)
          (hAk : ∀ z : Fin n → ℝ, (∀ i, ∑ j, A i j * z j = 0) → ∀ i j, z i = z j) 
          (hA1 : ∀ i, ∑ j, A i j = 0)
          (hAd : ∀ i, (∃ j, j ≠ i) → A i i ≠ 0)
          (hxA : ∀ θ : Profile Θ, (∀ i, (θ i : ℝ) ∈ B i) → ∀ i, x θ i = d i + ∑ j, A i j * v j (θ j))
          (g : (i : Fin n) → ↥(Θ i) → ℝ) 
          (hg : ∀ θ, ∑ i, g i (θ i) * x θ i = 0) :
           ∀ θ : Profile Θ, (∀ i, (θ i : ℝ) ∈ B i) → ∀ i, g i (θ i) = 0 := by
          have hupB : ∀ θ : Profile Θ, (∀ i, (θ i : ℝ) ∈ B i) → ∀ i (a : ↥(Θ i)), (a:ℝ) ∈ B i →
              ∀ k, ((Function.update θ i a) k : ℝ) ∈ B k := by
            intro θ hθ i a ha k
            by_cases hk : k = i
            · subst hk; simpa using ha
            · simpa [Function.update_of_ne hk] using hθ k
          have hupx : ∀ θ : Profile Θ, (∀ i, (θ i : ℝ) ∈ B i) → ∀ i (a : ↥(Θ i)), (a:ℝ) ∈ B i →
              ∀ k, x (Function.update θ i a) k = x θ k + A k i * (v i a - v i (θ i)) := by
            intro θ hθ i a ha k
            rw [hxA _ (hupB θ hθ i a ha), hxA θ hθ]
            have : ∑ j, A k j * v j (Function.update θ i a j) - ∑ j, A k j * v j (θ j) =
                A k i * (v i a - v i (θ i)) := by
              rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
              · simp; ring
              · intro j _ hj; simp [Function.update_of_ne hj]
              · simp
            linarith
          -- (*)
          have star : ∀ θ : Profile Θ, (∀ i, (θ i : ℝ) ∈ B i) → ∀ i (a : ↥(Θ i)), (a:ℝ) ∈ B i →
              (g i a - g i (θ i)) * x (Function.update θ i a) i +
                (v i a - v i (θ i)) * ∑ k, A i k * g k (θ k) = 0 := by
            intro θ hθ i a ha
            have h1 := hg (Function.update θ i a)
            have h2 := hg θ
            have h3 : ∑ k, (g k (Function.update θ i a k) - g k (θ k)) * x (Function.update θ i a) k =
               (g i a - g i (θ i)) * x (Function.update θ i a) i := by
              rw [Finset.sum_eq_single i]
              · simp
              · intro j _ hj; simp [Function.update_of_ne hj]
              · simp
            have h4 : ∑ k, g k (θ k) * x (Function.update θ i a) k = 
                ∑ k, g k (θ k) * x θ k + (v i a - v i (θ i)) * ∑ k, A i k * g k (θ k) := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun k _ => ?_)
              rw [hupx θ hθ i a ha k, hAs k i]; ring
            simp only [sub_mul, Finset.sum_sub_distrib] at h3
            rw [h4, h1, h2] at h3
            linarith
          have other : ∀ i : Fin n, ∀ a b : ℝ, ∃ c ∈ B i, c ≠ a ∧ c ≠ b := by
            intro i a b
            by_contra hcon
            push Not at hcon
            have : B i ⊆ {a, b} := by
              intro c hc
              by_cases h : c = a
              · simp [h]
              · simp [hcon c hc h]
            have h1 := Finset.card_le_card this
            have h2 := hB3 i
            have h3 : ({a, b} : Finset ℝ).card ≤ 2 := Finset.card_le_two
            omega
          -- G = 0
          have hG : ∀ θ : Profile Θ, (∀ i, (θ i : ℝ) ∈ B i) → ∀ i, ∑ k, A i k * g k (θ k) = 0 := by
            intro θ hθ i
            by_cases hex : ∃ j, j ≠ i
            · have hii := hAd i hex
              have hj : ∃ j, j ≠ i ∧ A i j ≠ 0 := by
                by_contra hcon
                push Not at hcon
                apply hii
                rw [← hA1 i, Finset.sum_eq_single i]
                · intro j _ hj; exact hcon j hj
                · simp
              obtain ⟨j, hji, hAij⟩ := hj
              obtain ⟨b, hbB, hb, _⟩ := other j (θ j) (θ j)
              obtain ⟨a, haB, ha, _⟩ := other i (θ i) (θ i)
              obtain ⟨a', haB', ha', haa'⟩ := other i (θ i) a
              let bb : ↥(Θ j) := ⟨b, hBs j hbB⟩
              have hvne : ∀ (k : Fin n) (c e : ℝ), c ∈ B k → e ∈ B k → c ≠ e → v k c - v k e ≠ 0 := by
                intro k c e hc he hce h0
                exact hce (hv k c (hBs k hc) e (hBs k he) (by linarith))
              have slope : ∀ c : ↥(Θ i), (c:ℝ) ∈ B i →
                  (g i c - g i (θ i)) * (v j b - v j (θ j)) + (v i c - v i (θ i)) * (g j bb - g j (θ j)) = 0 := by
                intro c hc
                have s1 := star θ hθ i c hc
                have hθ2 := hupB θ hθ j bb hbB
                have s2 := star _ hθ2 i c hc
                have e1 : (Function.update θ j bb) i = θ i := Function.update_of_ne (Ne.symm hji) _ _
                rw [e1] at s2
                have e2 : ∑ k, A i k * g k (Function.update θ j bb k) = ∑ k, A i k * g k (θ k) + A i j * (g j bb - g j (θ j)) := by
                  have : ∑ k, A i k * g k (Function.update θ j bb k) - ∑ k, A i k * g k (θ k) = A i j * (g j bb - g j (θ j)) := by
                    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
                    · simp; ring
                    · intro l _ hl; simp [Function.update_of_ne hl]
                    · simp
                  linarith
                have e3 : x (Function.update (Function.update θ j bb) i c) i = x (Function.update θ i c) i + A i j * (v j b - v j (θ j)) := by
                  rw [Function.update_comm hji.symm.symm, hupx _ (hupB θ hθ i c hc) j bb hbB i, Function.update_of_ne hji]
                rw [e2, e3] at s2
                have : A i j * ((g i c - g i (θ i)) * (v j b - v j (θ j)) + (v i c - v i (θ i)) * (g j bb - g j (θ j))) = 0 := by
                  linarith
                exact (mul_eq_zero.mp this).resolve_left hAij
              have hvj := hvne j b (θ j) hbB (hθ j) hb
              set σ := -(g j bb - g j (θ j)) / (v j b - v j (θ j)) with hσ
              have lin : ∀ c : ↥(Θ i), (c:ℝ) ∈ B i → (g i c - g i (θ i)) = σ * (v i c - v i (θ i)) := by
                intro c hc
                have := slope c hc
                rw [hσ]; field_simp; linarith
              have fin : ∀ c : ↥(Θ i), (c:ℝ) ∈ B i → (c:ℝ) ≠ θ i → 
                  σ * x (Function.update θ i c) i = - ∑ k, A i k * g k (θ k) := by
                intro c hc hcne
                have h1 := star θ hθ i c hc
                rw [lin c hc] at h1
                have h2 := hvne i c (θ i) hc (hθ i) hcne
                have : (v i c - v i (θ i)) * (σ * x (Function.update θ i c) i + ∑ k, A i k * g k (θ k)) = 0 := by
                  linarith
                have := (mul_eq_zero.mp this).resolve_left h2
                linarith
              have f1 := fin ⟨a, hBs i haB⟩ haB ha
              have f2 := fin ⟨a', hBs i haB'⟩ haB' ha'
              have u1 := hupx θ hθ i ⟨a, hBs i haB⟩ haB i
              have u2 := hupx θ hθ i ⟨a', hBs i haB'⟩ haB' i
              have h3 : σ * (A i i * (v i a' - v i a)) = 0 := by
                rw [u1] at f1; rw [u2] at f2
                simp only at f1 f2
                linarith
              have h4 : σ = 0 := (mul_eq_zero.mp h3).resolve_right
                (mul_ne_zero hii (hvne i a' a haB' haB haa'))
              rw [h4] at f1
              linarith
            · push Not at hex
              have : A i i = 0 := by
                rw [← hA1 i, Finset.sum_eq_single i]
                · intro j _ hj; exact absurd (hex j) hj
                · simp
              rw [Finset.sum_eq_single i]
              · simp [this]
              · intro j _ hj; exact absurd (hex j) hj
              · simp
          intro θ hθ i
          have h1 := hAk (fun k => g k (θ k)) (hG θ hθ)
          have h2 := hg θ
          have h3 : ∑ k, g k (θ k) * x θ k = g i (θ i) * ∑ k, x θ k := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun k _ => by rw [show g k (θ k) = g i (θ i) from h1 k i])
          rw [h3, hx1] at h2
          linarith
        have B2 (n : ℕ) (Θ : Fin n → Finset ℝ) (Q : Profile Θ → Finset (Fin n)) (hRIOM : RIOM Θ Q)
          (v : Fin n → ℝ → ℝ) (hv : ∀ i, StrictMonoOn (v i) (↑(Θ i) : Set ℝ))
          (x : Profile Θ → Fin n → ℝ) (hx1 : ∀ θ, ∑ i, x θ i = 1) (hx0 : ∀ θ i, 0 ≤ x θ i)
          (hxQ : ∀ θ i, i ∈ Q θ ↔ 0 < x θ i)
          (hmono : ∀ (θ : Profile Θ) i (a : ↥(Θ i)), (θ i : ℝ) ≤ a → x (Function.update θ i a) i ≤ x θ i)
          (d : Fin n → ℝ) (A : Fin n → Fin n → ℝ) (hAs : ∀ i j, A i j = A j i)
          (hAk : ∀ z : Fin n → ℝ, (∀ i, ∑ j, A i j * z j = 0) → ∀ i j, z i = z j) 
          (hA1 : ∀ i, ∑ j, A i j = 0)
          (hAd : ∀ i, (∃ j, j ≠ i) → A i i ≠ 0)
          (hxA : ∀ θ : Profile Θ, (∀ i, 0 < x θ i) → ∀ i, x θ i = d i + ∑ j, A i j * v j (θ j))
          (g : (i : Fin n) → ↥(Θ i) → ℝ) 
          (hg : ∀ θ, ∑ i, g i (θ i) * x θ i = 0) :
           ∀ θ : Profile Θ, ∀ i, 0 < x θ i → g i (θ i) = 0 := by
          obtain ⟨B, hBs, hBc, hBQ, hB3, hB5⟩ := hRIOM
          have hallpos : ∀ θ : Profile Θ, (∀ i, (θ i : ℝ) ∈ B i) → ∀ i, 0 < x θ i := by
            intro θ hθ i
            rw [← hxQ, hBQ θ hθ]; simp
          have hB := B1 n Θ B hBs hB3 v (fun i a ha b hb h => (hv i).injOn ha hb h) x hx1 d A hAs hAk hA1 hAd
            (fun θ hθ => hxA θ (hallpos θ hθ)) g hg
          have hne : ∀ i, ∃ c, c ∈ B i := by
            intro i
            have : 0 < (B i).card := by have := hB3 i; omega
            exact Finset.card_pos.mp this
          choose β hβ using hne
          let b0 : Profile Θ := fun i => ⟨β i, hBs i (hβ i)⟩
          have hb0 : ∀ i, (b0 i : ℝ) ∈ B i := hβ
          have hBin : ∀ i (c : ↥(Θ i)), (c:ℝ) ∈ B i → g i c = 0 := by
            intro i c hc
            have := hB (Function.update b0 i c) ?_ i
            · simpa using this
            · intro k
              by_cases hk : k = i
              · subst hk; simpa using hc
              · simpa [Function.update_of_ne hk] using hb0 k
          intro θ i hpos
          by_cases hlow : ∃ b ∈ B i, b ≤ (θ i : ℝ)
          · by_cases hhigh : ∃ b ∈ B i, (θ i : ℝ) ≤ b
            · obtain ⟨b, hb, hb1⟩ := hlow
              obtain ⟨e, he, he1⟩ := hhigh
              exact hBin i _ (hBc i b hb e he _ (θ i).2 hb1 he1)
            · push Not at hhigh
              have hup : (θ i : ℝ) ≤ activeUpper Θ Q i := by
                unfold activeUpper
                have hmem : (θ i : ℝ) ∈ (Θ i).filter (fun c => ∃ θ : Profile Θ, (θ i : ℝ) = c ∧ i ∈ Q θ) := by
                  rw [Finset.mem_filter]
                  exact ⟨(θ i).2, θ, rfl, (hxQ θ i).mpr hpos⟩
                have hS : ((Θ i).filter (fun c => ∃ θ : Profile Θ, (θ i : ℝ) = c ∧ i ∈ Q θ)).Nonempty := ⟨_, hmem⟩
                simp only []
                rw [dif_pos hS]
                exact Finset.le_max' _ _ hmem
              obtain ⟨fi, st, hfi, hiQ, hst, K, s, hs0, hsK, hs⟩ := hB5 i (θ i) (θ i).2 (fun b hb => (hhigh b hb).le) hup
              have ind : ∀ k, k ≤ K → ∀ j ∈ Q (s k), g j (s k j) = 0 := by
                intro k
                induction k with
                | zero =>
                  intro _ j _
                  rw [hs0]; exact hB st hst j
                | succ k ih =>
                  intro hk j hj
                  have ihk := ih (by omega)
                  obtain ⟨hsub, huniq⟩ := hs (k+1) (by omega) hk
                  simp only [Nat.add_sub_cancel] at hsub huniq
                  by_cases hch : s (k+1) j = s k j
                  · rw [hch]; exact ihk j (hsub hj)
                  · have hsum := hg (s (k+1))
                    rw [Finset.sum_eq_single j] at hsum
                    · exact (mul_eq_zero.mp hsum).resolve_right ((hxQ _ _).mp hj).ne'
                    · intro l _ hl
                      by_cases hlQ : l ∈ Q (s (k+1))
                      · have : s (k+1) l = s k l := by
                          by_contra hcl
                          exact hl (huniq l hlQ j hj hcl hch)
                        rw [this, ihk l (hsub hlQ), zero_mul]
                      · have : x (s (k+1)) l = 0 := by
                          have h1 := hx0 (s (k+1)) l
                          have h2 : ¬ 0 < x (s (k+1)) l := fun h => hlQ ((hxQ _ _).mpr h)
                          linarith
                        rw [this, mul_zero]
                    · simp
              have h1 := ind K le_rfl i (by rw [hsK]; exact hiQ)
              rw [hsK] at h1
              have : fi i = θ i := Subtype.ext hfi
              rwa [this] at h1
          · push Not at hlow
            have h1 := hmono (Function.update b0 i (θ i)) i (b0 i) (by simpa using (hlow _ (hb0 i)).le)
            have h2 : Function.update (Function.update b0 i (θ i)) i (b0 i) = b0 := by simp
            rw [h2] at h1
            have h3 := hallpos b0 hb0 i
            have h4 := hg (Function.update b0 i (θ i))
            rw [Finset.sum_eq_single i] at h4
            · have := (mul_eq_zero.mp h4).resolve_right (lt_of_lt_of_le h3 h1).ne'
              simpa using this
            · intro l _ hl
              rw [Function.update_of_ne hl, hBin l _ (hb0 l), zero_mul]
            · simp
        have C0 : ∀ (S : Finset ℝ) (P : ℝ → Prop),
            (∀ c ∈ S, (S.filter (c < ·)) = ∅ → P c) →
            (∀ c ∈ S, ∀ e ∈ S, c < e → S.filter (c < ·) = insert e (S.filter (e < ·)) →
               (S.filter (· < e)).Nonempty → (∀ h : (S.filter (· < e)).Nonempty, (S.filter (· < e)).max' h = c) → P e → P c) →
            ∀ c ∈ S, P c := by
          intro S P h0 h1
          have : ∀ N : ℕ, ∀ c ∈ S, (S.filter (c < ·)).card = N → P c := by
            intro N
            induction N with
            | zero => 
              intro c hc h
              exact h0 c hc (Finset.card_eq_zero.mp h)
            | succ N ih =>
              intro c hc h
              have hne : (S.filter (c < ·)).Nonempty := by
                rw [← Finset.card_pos]; omega
              set e := (S.filter (c < ·)).min' hne with he
              have hem := Finset.min'_mem _ hne
              rw [← he, Finset.mem_filter] at hem
              have hins : S.filter (c < ·) = insert e (S.filter (e < ·)) := by
                ext z
                simp only [Finset.mem_filter, Finset.mem_insert]
                constructor
                · rintro ⟨hz, hcz⟩
                  have : e ≤ z := Finset.min'_le _ _ (by simp [hz, hcz])
                  rcases this.lt_or_eq with h | h
                  · exact Or.inr ⟨hz, h⟩
                  · exact Or.inl h.symm
                · rintro (h | ⟨hz, h⟩)
                  · rw [h]; exact hem
                  · exact ⟨hz, hem.2.trans h⟩
              have hcm : c ∈ S.filter (· < e) := by simp [hc, hem.2]
              refine h1 c hc e hem.1 hem.2 hins ⟨c, hcm⟩ ?_ (ih e hem.1 ?_)
              · intro hh
                apply le_antisymm
                · apply Finset.max'_le
                  intro z hz
                  rw [Finset.mem_filter] at hz
                  by_contra hcz
                  push Not at hcz
                  have : e ≤ z := Finset.min'_le _ _ (by simp [hz.1, hcz])
                  linarith [hz.2]
                · exact Finset.le_max' _ _ hcm
              · rw [hins, Finset.card_insert_of_notMem (by simp)] at h
                omega
          intro c hc
          exact this _ c hc rfl
        have C1 (n : ℕ) (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ) (hf : ∀ i, ∀ c ∈ Θ i, 0 < f i c)
          (C0 : ∀ (S : Finset ℝ) (P : ℝ → Prop),
            (∀ c ∈ S, (S.filter (c < ·)) = ∅ → P c) →
            (∀ c ∈ S, ∀ e ∈ S, c < e → S.filter (c < ·) = insert e (S.filter (e < ·)) →
               (S.filter (· < e)).Nonempty → (∀ h : (S.filter (· < e)).Nonempty, (S.filter (· < e)).max' h = c) → P e → P c) →
            ∀ c ∈ S, P c) :
           ∀ i, ∀ X : ℝ → ℝ,
             (∑ c ∈ Θ i, f i c * (c * X c + ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * X b) 
               = ∑ c ∈ Θ i, f i c * (virtualCost Θ f i c * X c)) ∧
             (∀ T : ℝ → ℝ, (∀ a ∈ Θ i, ∀ b ∈ Θ i, T b - a * X b ≤ T a - a * X a) → (∀ a ∈ Θ i, 0 ≤ T a - a * X a) →
                ∑ c ∈ Θ i, f i c * (virtualCost Θ f i c * X c) ≤ ∑ c ∈ Θ i, f i c * T c) ∧
             (∀ T : ℝ → ℝ, (∀ c ∈ Θ i, 0 ≤ X c) → (∀ a ∈ Θ i, ∀ b ∈ Θ i, a ≤ b → X b ≤ X a) → 
               (∀ c ∈ Θ i, T c = c * X c + ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * X b) → 
               (∀ a ∈ Θ i, ∀ b ∈ Θ i, T b - a * X b ≤ T a - a * X a) ∧ (∀ a ∈ Θ i, 0 ≤ T a - a * X a)) := by
          intro i X
          have hpred : ∀ c e, (Θ i).filter (· < e) = (Θ i).filter (· < e) → ((Θ i).filter (· < e)).Nonempty →
              (∀ h : ((Θ i).filter (· < e)).Nonempty, ((Θ i).filter (· < e)).max' h = c) → pred Θ i e = c := by
            intro c e _ hne h
            unfold pred
            rw [dif_pos hne]
            exact h hne
          have hple : ∀ b, pred Θ i b ≤ b := by
            intro b
            unfold pred
            split_ifs with h
            · have := Finset.max'_mem _ h
              rw [Finset.mem_filter] at this
              exact this.2.le
            · exact le_rfl
          have hF : ∀ b ∈ Θ i, (∑ c ∈ (Θ i).filter (· < b), f i c) * (b - pred Θ i b) =
              cdfF Θ f i (pred Θ i b) * (b - pred Θ i b) := by
            intro b hb
            by_cases h : ((Θ i).filter (· < b)).Nonempty
            · congr 1
              unfold cdfF
              have hp : pred Θ i b = ((Θ i).filter (· < b)).max' h := by unfold pred; rw [dif_pos h]
              have hm := Finset.max'_mem _ h
              rw [← hp, Finset.mem_filter] at hm
              apply Finset.sum_congr _ (fun _ _ => rfl)
              ext z
              simp only [Finset.mem_filter]
              constructor
              · rintro ⟨hz, hzb⟩
                refine ⟨hz, ?_⟩
                rw [hp]
                exact Finset.le_max' _ _ (by simp [hz, hzb])
              · rintro ⟨hz, hzb⟩
                exact ⟨hz, lt_of_le_of_lt hzb hm.2⟩
            · have hp : pred Θ i b = b := by unfold pred; rw [dif_neg h]
              rw [hp]; simp
          have part1 : ∑ c ∈ Θ i, f i c * (c * X c + ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * X b) 
               = ∑ c ∈ Θ i, f i c * (virtualCost Θ f i c * X c) := by
            have h1 : ∑ c ∈ Θ i, f i c * ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * X b =
               ∑ b ∈ Θ i, cdfF Θ f i (pred Θ i b) * (b - pred Θ i b) * X b := by
              simp only [Finset.sum_filter, Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl (fun b hb => ?_)
              rw [← hF b hb, Finset.sum_filter, Finset.sum_mul, Finset.sum_mul]
              refine Finset.sum_congr rfl (fun c hc => ?_)
              split_ifs <;> ring
            simp only [mul_add, Finset.sum_add_distrib]
            rw [h1, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun c hc => ?_)
            have := (hf i c hc).ne'
            unfold virtualCost
            field_simp
          refine ⟨part1, ?_, ?_⟩
          · intro T hIC hIR
            rw [← part1]
            refine Finset.sum_le_sum (fun c hc => mul_le_mul_of_nonneg_left ?_ (hf i c hc).le)
            refine C0 (Θ i) (fun c => c * X c + ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * X b ≤ T c) ?_ ?_ c hc
            · intro c hc he
              have := hIR c hc
              simp only [he, Finset.sum_empty]
              linarith
            · intro c hc e he hce hins hne hmax hP
              simp only [hins]
              rw [Finset.sum_insert (by simp), hpred c e rfl hne hmax]
              have := hIC c hc e he
              have := mul_comm 1 (X e)
              nlinarith
          · intro T hX0 hXm hT
            have hW : ∀ c e, c ∈ Θ i → e ∈ Θ i → (Θ i).filter (c < ·) = insert e ((Θ i).filter (e < ·)) →
                pred Θ i e = c → T c = c * X c + (e - c) * X e + (T e - e * X e) := by
              intro c e hc he hins hp
              rw [hT c hc, hT e he, hins, Finset.sum_insert (by simp), hp]; ring
            constructor
            · intro a ha b hb
              rcases le_total a b with hab | hab
              · refine C0 (Θ i) (fun a => a ≤ b → T b - a * X b ≤ T a - a * X a) ?_ ?_ a ha hab
                · intro c hc he hcb
                  rcases hcb.lt_or_eq with h | h
                  · exfalso
                    have : b ∈ (Θ i).filter (c < ·) := by simp [hb, h]
                    rw [he] at this; simp at this
                  · rw [h]
                · intro c hc e he hce hins hne hmax hP hcb
                  rcases hcb.lt_or_eq with h | h
                  · have hbm : b ∈ (Θ i).filter (c < ·) := by simp [hb, h]
                    rw [hins] at hbm
                    have heb : e ≤ b := by
                      simp at hbm
                      rcases hbm with h | h
                      · exact h.ge
                      · exact h.2.le
                    have h1 := hP heb
                    have h2 := hW c e hc he hins (hpred c e rfl hne hmax)
                    have h3 := hXm e he b hb heb
                    nlinarith
                  · rw [h]
              · refine C0 (Θ i) (fun b => b ≤ a → T b - a * X b ≤ T a - a * X a) ?_ ?_ b hb hab
                · intro c hc he hcb
                  rcases hcb.lt_or_eq with h | h
                  · exfalso
                    have : a ∈ (Θ i).filter (c < ·) := by simp [ha, h]
                    rw [he] at this; simp at this
                  · rw [h]
                · intro c hc e he hce hins hne hmax hP hcb
                  rcases hcb.lt_or_eq with h | h
                  · have hbm : a ∈ (Θ i).filter (c < ·) := by simp [ha, h]
                    rw [hins] at hbm
                    have heb : e ≤ a := by
                      simp at hbm
                      rcases hbm with h | h
                      · exact h.ge
                      · exact h.2.le
                    have h1 := hP heb
                    have h2 := hW c e hc he hins (hpred c e rfl hne hmax)
                    have h3 := hXm c hc e he hce.le
                    nlinarith
                  · rw [h]
            · intro a ha
              rw [hT a ha]
              have : 0 ≤ ∑ b ∈ (Θ i).filter (a < ·), (b - pred Θ i b) * X b := by
                apply Finset.sum_nonneg
                intro b hb
                rw [Finset.mem_filter] at hb
                exact mul_nonneg (by linarith [hple b]) (hX0 b hb.1)
              linarith
        have C2 (n : ℕ) (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ) :
           ∀ (i : Fin n) (h : ℝ → ℝ) (u : Profile Θ → ℝ), expect f (fun θ => h (θ i) * u θ) = 
              ∑ c ∈ Θ i, f i c * (h c * interim f u i c) := by
          intro i h u
          unfold expect interim
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun θ _ => ?_)
          rw [Finset.sum_eq_single (θ i : ℝ)]
          · rw [if_pos rfl]
            unfold prob probOthers
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
            ring
          · intro c _ hc
            rw [if_neg (Ne.symm hc)]; ring
          · intro h; exact absurd (θ i).2 h
        have C3 (n : ℕ) (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ) :
           ∀ (x t : Profile Θ → Fin n → ℝ) (i : Fin n) (a b : ℝ), utility f x t i b a = 
              interim f (fun θ => t θ i) i b - a * interim f (fun θ => x θ i) i b := by
          intro x t i a b
          unfold utility interim
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun θ _ => ?_)
          split_ifs <;> ring
        obtain ⟨hne, hcpos, hf, hf1⟩ := hTypes
        set v : Fin n → ℝ → ℝ := virtualCost Θ f with hv
        obtain ⟨x, hxdef⟩ : ∃ x, x = affX M Θ f := ⟨_, rfl⟩
        have hx : ∀ θ, x θ ∈ simplex n ∧ ∀ y ∈ simplex n, CS M.gcs y (vvec Θ f θ) ≤ CS M.gcs (x θ) (vvec Θ f θ) := by
          intro θ
          rw [hxdef]
          exact A1 n hn M (vvec Θ f θ)
        have hx0 : ∀ θ i, 0 ≤ x θ i := fun θ i => (hx θ).1.1 i
        have hx1 : ∀ θ, ∑ i, x θ i = 1 := fun θ => (hx θ).1.2
        have hxQ : ∀ θ i, i ∈ affQ M Θ f θ ↔ 0 < x θ i := by
          intro θ i
          rw [hxdef]
          simp [affQ, QuadraticMarket.active, affX]
        have hmono : ∀ (θ : Profile Θ) i (a : ↥(Θ i)), (θ i : ℝ) ≤ a → x (Function.update θ i a) i ≤ x θ i := by
          intro θ i a ha
          rcases ha.lt_or_eq with hlt | heq
          · have hvlt : v i (θ i) < v i a := hReg i (θ i).2 a.2 hlt
            have h1 := (hx θ).2 _ (hx (Function.update θ i a)).1
            have h2 := (hx (Function.update θ i a)).2 _ (hx θ).1
            unfold CS at h1 h2
            have key : ∀ z : Fin n → ℝ, ∑ j, vvec Θ f (Function.update θ i a) j * z j =
                ∑ j, vvec Θ f θ j * z j + (v i a - v i (θ i)) * z i := by
              intro z
              have : ∑ j, vvec Θ f (Function.update θ i a) j * z j - ∑ j, vvec Θ f θ j * z j =
                (v i a - v i (θ i)) * z i := by
                rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
                · simp [vvec, hv]; ring
                · intro j _ hj; simp [vvec, Function.update_of_ne hj]
                · simp
              linarith
            rw [key, key] at h2
            have h3 : (v i a - v i (θ i)) * (x (Function.update θ i a) i) ≤ (v i a - v i (θ i)) * (x θ i) := by
              linarith
            exact le_of_mul_le_mul_left h3 (by linarith)
          · have : a = θ i := Subtype.ext heq.symm
            rw [this, Function.update_eq_self]
        have hpo : ∀ i θ, 0 < probOthers (Θ := Θ) f i θ := by
          intro i θ
          exact Finset.prod_pos (fun j _ => hf j _ (θ j).2)
        have hprob : ∀ θ, 0 < prob (Θ := Θ) f θ := by
          intro θ
          exact Finset.prod_pos (fun j _ => hf j _ (θ j).2)
        have hprobi : ∀ i θ, prob (Θ := Θ) f θ = f i (θ i) * probOthers f i θ := by
          intro i θ
          unfold prob probOthers
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
        obtain ⟨X, hX⟩ : ∃ X : Fin n → ℝ → ℝ, ∀ i c, X i c = interim f (fun θ => x θ i) i c := ⟨_, fun _ _ => rfl⟩
        have hX0 : ∀ i c, 0 ≤ X i c := by
          intro i c
          rw [hX]
          refine Finset.sum_nonneg (fun θ _ => ?_)
          split_ifs
          · exact mul_nonneg (hpo i θ).le (hx0 θ i)
          · exact le_rfl
        have hXm : ∀ i, ∀ a ∈ Θ i, ∀ b ∈ Θ i, a ≤ b → X i b ≤ X i a := by
          intro i a ha b hb hab
          rw [hX, hX]
          unfold interim
          rw [← Finset.sum_filter, ← Finset.sum_filter]
          have hpoup : ∀ (θ : Profile Θ) (c : ↥(Θ i)), probOthers f i (Function.update θ i c) = probOthers f i θ := by
            intro θ c
            unfold probOthers
            refine Finset.prod_congr rfl (fun j hj => ?_)
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
          have hre : ∑ θ ∈ Finset.univ.filter (fun θ : Profile Θ => (θ i : ℝ) = b), probOthers f i θ * x θ i =
              ∑ θ ∈ Finset.univ.filter (fun θ : Profile Θ => (θ i : ℝ) = a), 
                probOthers f i θ * x (Function.update θ i ⟨b, hb⟩) i := by
            refine Finset.sum_nbij' (fun θ => Function.update θ i ⟨a, ha⟩) (fun θ => Function.update θ i ⟨b, hb⟩) ?_ ?_ ?_ ?_ ?_
            · intro θ _; simp
            · intro θ _; simp
            · intro θ hθ
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
              have : (⟨b, hb⟩ : ↥(Θ i)) = θ i := Subtype.ext hθ.symm
              simp [this]
            · intro θ hθ
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
              have : (⟨a, ha⟩ : ↥(Θ i)) = θ i := Subtype.ext hθ.symm
              simp [this]
            · intro θ hθ
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
              have : (⟨b, hb⟩ : ↥(Θ i)) = θ i := Subtype.ext hθ.symm
              simp [this, hpoup]
          rw [hre]
          refine Finset.sum_le_sum (fun θ hθ => mul_le_mul_of_nonneg_left ?_ (hpo i θ).le)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
          exact hmono θ i ⟨b, hb⟩ (by rw [hθ]; exact hab)
        obtain ⟨T, hT⟩ : ∃ T : Fin n → ℝ → ℝ, ∀ i c, T i c = c * X i c + ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * X i b :=
          ⟨_, fun _ _ => rfl⟩
        obtain ⟨d, A, hAs, hAk, hA1, hAd, hAx⟩ := A3 n hn M hM (A2 n M hM)
        have hlam : ∃ lam : Profile Θ → ℝ, ∀ k : (Σ i : Fin n, ↥(Θ i)), 
            ∑ θ : Profile Θ, (if ((θ k.1 : ℝ) = k.2) then probOthers f k.1 θ * x θ k.1 else 0) * lam θ
              = T k.1 k.2 - v k.1 k.2 * X k.1 k.2 := by
          refine D1 (Σ i : Fin n, ↥(Θ i)) (Profile Θ) (fun k θ => if ((θ k.1 : ℝ) = k.2) then probOthers f k.1 θ * x θ k.1 else 0)
            (fun k => T k.1 k.2 - v k.1 k.2 * X k.1 k.2) ?_
          intro y hy
          have hg : ∀ θ : Profile Θ, ∑ i, (y ⟨i, θ i⟩ / f i (θ i)) * x θ i = 0 := by
            intro θ
            have h1 := hy θ
            rw [Fintype.sum_sigma] at h1
            have h2 : ∀ i : Fin n, ∑ c : ↥(Θ i), y ⟨i, c⟩ * (if ((θ i : ℝ) = c) then probOthers f i θ * x θ i else 0) =
                prob f θ * ((y ⟨i, θ i⟩ / f i (θ i)) * x θ i) := by
              intro i
              rw [Finset.sum_eq_single (θ i)]
              · rw [if_pos rfl, hprobi i θ]
                have := (hf i _ (θ i).2).ne'
                field_simp
              · intro c _ hc
                rw [if_neg (fun h => hc (Subtype.ext h.symm)), mul_zero]
              · simp
            simp only [h2] at h1
            rw [← Finset.mul_sum] at h1
            exact (mul_eq_zero.mp h1).resolve_left (hprob θ).ne'
          have hzero := B2 n Θ (affQ M Θ f) hRIOM v hReg x hx1 hx0 hxQ hmono d A hAs hAk hA1 hAd
            (fun θ hθ => hAx (vvec Θ f θ) (x θ) (hx θ).1 (hx θ).2 hθ) (fun i c => y ⟨i, c⟩ / f i c) hg
          refine Finset.sum_eq_zero (fun k _ => ?_)
          obtain ⟨i, c⟩ := k
          by_cases hact : ∃ θ : Profile Θ, θ i = c ∧ 0 < x θ i
          · obtain ⟨θ, hθ, hp⟩ := hact
            have h1 := hzero θ i hp
            rw [hθ] at h1
            have h2 : y ⟨i, c⟩ = 0 := by
              rcases div_eq_zero_iff.mp h1 with h | h
              · exact h
              · exact absurd h (hf i c c.2).ne'
            rw [h2, zero_mul]
          · push Not at hact
            have h1 : X i c = 0 := by
              rw [hX]
              refine Finset.sum_eq_zero (fun θ _ => ?_)
              split_ifs with h
              · have h3 : x θ i = 0 := le_antisymm (hact θ (Subtype.ext h)) (hx0 θ i)
                simp only [h3, mul_zero]
              · rfl
            have h2 : T i c = 0 := by
              rw [hT, h1, mul_zero, zero_add]
              refine Finset.sum_eq_zero (fun b hb => ?_)
              rw [Finset.mem_filter] at hb
              have : X i b = 0 := le_antisymm (by rw [← h1]; exact hXm i c c.2 b hb.1 hb.2.le) (hX0 i b)
              rw [this, mul_zero]
            simp only [h1, h2]
            ring
        obtain ⟨lam, hlam⟩ := hlam
        obtain ⟨p, hp⟩ : ∃ p : Profile Θ → Fin n → ℝ, ∀ θ i, p θ i = vvec Θ f θ i + lam θ := ⟨_, fun _ _ => rfl⟩
        have hPT : ∀ i, ∀ c ∈ Θ i, interim f (fun θ => p θ i * x θ i) i c = T i c := by
          intro i c hc
          have h1 := hlam ⟨i, ⟨c, hc⟩⟩
          simp only at h1
          have h2 : interim f (fun θ => p θ i * x θ i) i c = v i c * X i c + 
             ∑ θ : Profile Θ, (if ((θ i : ℝ) = c) then probOthers f i θ * x θ i else 0) * lam θ := by
            rw [hX]
            unfold interim
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun θ _ => ?_)
            split_ifs with h
            · simp only [hp]
              have : vvec Θ f θ i = v i c := by simp [vvec, hv, h]
              rw [this]; ring
            · ring
          rw [h2, h1]; ring
        have hCentFeas : IsCentFeasible f (simplex n) x (fun θ i => p θ i * x θ i) := by
          have h := fun i => (C1 n Θ f hf C0 i (X i)).2.2 (fun c => interim f (fun θ => p θ i * x θ i) i c) (fun c _ => hX0 i c) (hXm i)
            (fun c hc => by rw [← hT]; exact hPT i c hc)
          refine ⟨?_, ?_, fun θ => (hx θ).1⟩
          · intro i a ha b hb
            rw [C3, C3, ← hX, ← hX]
            exact (h i).1 a ha b hb
          · intro i a ha
            rw [C3, ← hX]
            exact (h i).2 a ha
        have hDecFeas : IsDecLinFeasible f M.gcs (simplex n) (fun _ => Finset.univ) p x := by
          refine ⟨hCentFeas, fun θ => ⟨(hx θ).1, by simp, ?_⟩⟩
          intro z hz _
          have h1 := (hx θ).2 z hz
          have h2 : ∀ w ∈ simplex n, CS M.gcs w (p θ) = CS M.gcs w (vvec Θ f θ) - lam θ := by
            intro w hw
            unfold CS
            simp only [hp, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hw.2]
            ring
          rw [h2 z hz, h2 _ (hx θ).1]
          linarith
        have hobj : ∀ (x t : Profile Θ → Fin n → ℝ), centObj f M.gcs x t = 
            expect f (fun θ => M.gcs (x θ)) - ∑ i, ∑ c ∈ Θ i, f i c * interim f (fun θ => t θ i) i c := by
          intro x t
          have h1 : ∀ i, ∑ c ∈ Θ i, f i c * interim f (fun θ => t θ i) i c = expect f (fun θ => t θ i) := by
            intro i
            have := C2 n Θ f i (fun _ => 1) (fun θ => t θ i)
            simp only [one_mul] at this
            exact this.symm
          simp only [h1]
          unfold centObj expect
          rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun θ _ => ?_)
          rw [mul_sub, Finset.mul_sum]
        have hobjv : ∀ (x : Profile Θ → Fin n → ℝ), expect f (fun θ => CS M.gcs (x θ) (vvec Θ f θ)) = 
            expect f (fun θ => M.gcs (x θ)) - ∑ i, ∑ c ∈ Θ i, f i c * (v i c * interim f (fun θ => x θ i) i c) := by
          intro x
          have h1 : ∀ i, ∑ c ∈ Θ i, f i c * (v i c * interim f (fun θ => x θ i) i c) = expect f (fun θ => vvec Θ f θ i * x θ i) := by
            intro i
            exact (C2 n Θ f i (v i) (fun θ => x θ i)).symm
          simp only [h1]
          unfold CS expect
          rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun θ _ => ?_)
          rw [mul_sub, Finset.mul_sum]
        set V := expect f (fun θ => CS M.gcs (x θ) (vvec Θ f θ)) with hV
        have hub : ∀ x' t' : Profile Θ → Fin n → ℝ, IsCentFeasible f (simplex n) x' t' → centObj f M.gcs x' t' ≤ V := by
          intro x' t' h
          have h1 : centObj f M.gcs x' t' ≤ expect f (fun θ => CS M.gcs (x' θ) (vvec Θ f θ)) := by
            rw [hobj, hobjv]
            refine sub_le_sub_left (Finset.sum_le_sum (fun i _ => ?_)) _
            refine (C1 n Θ f hf C0 i (fun c => interim f (fun θ => x' θ i) i c)).2.1 (fun c => interim f (fun θ => t' θ i) i c) ?_ ?_
            · intro a ha b hb
              have := h.1 i a ha b hb
              rwa [C3, C3] at this
            · intro a ha
              have := h.2.1 i a ha
              rwa [C3] at this
          refine h1.trans ?_
          rw [hV]
          refine Finset.sum_le_sum (fun θ _ => mul_le_mul_of_nonneg_left ?_ (hprob θ).le)
          exact (hx θ).2 _ (h.2.2 θ)
        have hval : decLinObj f M.gcs p x = V := by
          have h0 : decLinObj f M.gcs p x = centObj f M.gcs x (fun θ i => p θ i * x θ i) := rfl
          rw [h0, hobj, hV, hobjv]
          congr 1
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have h1 := (C1 n Θ f hf C0 i (X i)).1
          simp only [← hX]
          rw [← h1]
          refine Finset.sum_congr rfl (fun c hc => ?_)
          rw [hPT i c hc, hT]
        have gC : IsGreatest {r | ∃ x t : Profile Θ → Fin n → ℝ,
            IsCentFeasible f (simplex n) x t ∧ r = centObj f M.gcs x t} V := by
          refine ⟨⟨x, _, hCentFeas, hval.symm⟩, ?_⟩
          rintro r ⟨x', t', h, rfl⟩
          exact hub x' t' h
        have gD : IsGreatest {r | ∃ (q : Profile Θ → Finset (Fin n)) (p x : Profile Θ → Fin n → ℝ),
            IsDecLinFeasible f M.gcs (simplex n) q p x ∧ r = decLinObj f M.gcs p x} V := by
          refine ⟨⟨_, p, x, hDecFeas, hval.symm⟩, ?_⟩
          rintro r ⟨q', p', x', h, rfl⟩
          exact hub x' _ h.1
        refine ⟨?_, ?_⟩
        · unfold optDecLin optCent
          rw [gC.csSup_eq, gD.csSup_eq]
        · exact ⟨⟨V, gC.1⟩, ⟨V, gC.2⟩, ⟨V, gD.1⟩, ⟨V, gD.2⟩⟩
