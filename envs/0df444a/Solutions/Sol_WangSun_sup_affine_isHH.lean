-- Prove2me | solution 1 for WangSun.sup_affine_isHH
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T13:11:08.189068+00:00
-- url     : https://prove2.me/submissions/1ada5609-4a5f-4781-9d7f-326639c6637d

import Definitions.Def_WangSunCPWL

open Finset

variable {n : ℕ}

namespace WSHR

/-! ### Closure properties of `IsHH` -/

private theorem isHinge_neg {h : (Fin n → ℝ) → ℝ} (hh : IsHinge h) : IsHinge (-h) := by
  obtain ⟨σ, L, hσ, rfl⟩ := hh
  refine ⟨-σ, L, ?_, ?_⟩
  · rcases hσ with h | h <;> simp [h]
  · funext x
    simp

private theorem isHH_neg {f : (Fin n → ℝ) → ℝ} (hf : IsHH f) : IsHH (-f) := by
  obtain ⟨K, h, hh, rfl⟩ := hf
  exact ⟨K, fun k => -(h k), fun k => isHinge_neg (hh k), by simp⟩

private theorem isHH_add {f g : (Fin n → ℝ) → ℝ} (hf : IsHH f) (hg : IsHH g) :
    IsHH (fun x => f x + g x) := by
  obtain ⟨K1, h1, hh1, e1⟩ := hf
  obtain ⟨K2, h2, hh2, e2⟩ := hg
  refine ⟨K1 + K2, Fin.append h1 h2, ?_, ?_⟩
  · intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [Fin.append_left]; exact hh1 i
    · rw [Fin.append_right]; exact hh2 i
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← e1, ← e2]
    rfl

private theorem isHH_zero : IsHH (fun _ : Fin n → ℝ => (0 : ℝ)) :=
  ⟨0, fun k => k.elim0, fun k => k.elim0, by funext x; simp⟩

private theorem isHH_sum {κ : Type} (t : Finset κ) (F : κ → ((Fin n → ℝ) → ℝ))
    (hF : ∀ k ∈ t, IsHH (F k)) : IsHH (fun x => ∑ k ∈ t, F k x) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using isHH_zero
  | insert a s ha ih =>
      have h1 : IsHH (F a) := hF a (mem_insert_self a s)
      have h2 : IsHH (fun x => ∑ k ∈ s, F k x) :=
        ih fun k hk => hF k (mem_insert_of_mem hk)
      have := isHH_add h1 h2
      simpa [Finset.sum_insert ha] using this

/-! ### Maxima over finsets -/

variable {ι : Type}

/-- The pointwise maximum of `L` over a finset, with junk value `0` on the empty set. -/
private noncomputable def mx (L : ι → ((Fin n → ℝ) →ᵃ[ℝ] ℝ)) (t : Finset ι) :
    (Fin n → ℝ) → ℝ :=
  fun x => if h : t.Nonempty then t.sup' h (fun i => L i x) else 0

private theorem mx_eq (L : ι → ((Fin n → ℝ) →ᵃ[ℝ] ℝ)) {t : Finset ι} (h : t.Nonempty)
    (x : Fin n → ℝ) : mx L t x = t.sup' h (fun i => L i x) := by
  simp [mx, h]

private theorem affine_decomp (f : (Fin n → ℝ) →ᵃ[ℝ] ℝ) (x : Fin n → ℝ) :
    f x = f.linear x + f 0 := by
  have h := congrFun (AffineMap.decomp f) x
  simpa using h

/-! ### The base case: at most `n + 1` affine arguments is a single hinge -/

private theorem isHH_mx_small (L : ι → ((Fin n → ℝ) →ᵃ[ℝ] ℝ)) (t : Finset ι)
    (ht : t.Nonempty) (hcard : t.card ≤ n + 1) : IsHH (mx L t) := by
  classical
  have hpos : 0 < t.card := Finset.card_pos.mpr ht
  let φ : Fin (n + 1) → ι := fun j =>
    if h : (j : ℕ) < t.card then (t.equivFin.symm ⟨(j : ℕ), h⟩ : ι)
    else (t.equivFin.symm ⟨0, hpos⟩ : ι)
  have hmem : ∀ j, φ j ∈ t := by
    intro j
    by_cases h : (j : ℕ) < t.card
    · simpa [φ, h] using (t.equivFin.symm ⟨(j : ℕ), h⟩).2
    · simpa [φ, h] using (t.equivFin.symm ⟨0, hpos⟩).2
  have hsurj : ∀ i ∈ t, ∃ j, φ j = i := by
    intro i hi
    refine ⟨⟨((t.equivFin ⟨i, hi⟩ : Fin t.card) : ℕ),
      lt_of_lt_of_le (t.equivFin ⟨i, hi⟩).isLt hcard⟩, ?_⟩
    have h : (((t.equivFin ⟨i, hi⟩ : Fin t.card) : ℕ)) < t.card := (t.equivFin ⟨i, hi⟩).isLt
    simp only [φ, h, dif_pos, Fin.eta]
    simp
  have hval : ∀ x, t.sup' ht (fun i => L i x)
      = (univ : Finset (Fin (n + 1))).sup' univ_nonempty (fun j => L (φ j) x) := by
    intro x
    apply le_antisymm
    · refine Finset.sup'_le _ _ fun i hi => ?_
      obtain ⟨j, hj⟩ := hsurj i hi
      have hle := Finset.le_sup' (fun j => L (φ j) x) (mem_univ j)
      rwa [hj] at hle
    · exact Finset.sup'_le _ _ fun j _ => Finset.le_sup' (fun i => L i x) (hmem j)
  refine ⟨1, ![fun x => (1 : ℝ) *
    (univ : Finset (Fin (n + 1))).sup' univ_nonempty (fun j => L (φ j) x)], ?_, ?_⟩
  · intro k
    fin_cases k
    exact ⟨1, fun j => L (φ j), Or.inl rfl, rfl⟩
  · funext x
    rw [Fin.sum_univ_one]
    simp only [Matrix.cons_val_zero]
    rw [mx_eq L ht x, hval x, one_mul]

/-! ### The splitting lemma -/

private theorem split (L : ι → ((Fin n → ℝ) →ᵃ[ℝ] ℝ)) (t : Finset ι) [DecidableEq ι]
    (hbig : n + 2 ≤ t.card) :
    ∃ A : Finset ι, A ⊆ t ∧ A.Nonempty ∧ (t \ A).Nonempty ∧
      ∀ x, ∃ i ∈ A, ∃ j ∈ t \ A, L i x ≤ L j x := by
  classical
  by_cases hnotinj : ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ (L i).linear = (L j).linear
  · obtain ⟨i, hi, j, hj, hij, hlin⟩ := hnotinj
    rcases le_total ((L i) 0) ((L j) 0) with hle | hle
    · refine ⟨{i}, by simpa using hi, ⟨i, mem_singleton_self i⟩,
        ⟨j, mem_sdiff.2 ⟨hj, by simp [Ne.symm hij]⟩⟩, fun x => ?_⟩
      refine ⟨i, mem_singleton_self i, j, mem_sdiff.2 ⟨hj, by simp [Ne.symm hij]⟩, ?_⟩
      rw [affine_decomp (L i) x, affine_decomp (L j) x, hlin]
      linarith
    · refine ⟨{j}, by simpa using hj, ⟨j, mem_singleton_self j⟩,
        ⟨i, mem_sdiff.2 ⟨hi, by simp [hij]⟩⟩, fun x => ?_⟩
      refine ⟨j, mem_singleton_self j, i, mem_sdiff.2 ⟨hi, by simp [hij]⟩, ?_⟩
      rw [affine_decomp (L i) x, affine_decomp (L j) x, hlin]
      linarith
  · push_neg at hnotinj
    have hinj : ∀ a ∈ t, ∀ b ∈ t, (L a).linear = (L b).linear → a = b := by
      intro a ha b hb hab
      by_contra hne
      exact hnotinj a ha b hb hne hab
    have hinj' : Set.InjOn (fun i => (L i).linear) (↑t : Set ι) :=
      fun a ha b hb hab => hinj a ha b hb hab
    have hfr : Module.finrank ℝ ((Fin n → ℝ) →ₗ[ℝ] ℝ) = n := by simp
    set T := t.image (fun i => (L i).linear) with hT
    have hTcard : T.card = t.card := Finset.card_image_of_injOn hinj'
    have hlt : Module.finrank ℝ ((Fin n → ℝ) →ₗ[ℝ] ℝ) + 1 < T.card := by
      rw [hTcard, hfr]; omega
    obtain ⟨fw, hrel, htot, x₀, hx₀T, hx₀pos⟩ :=
      FiniteDimensional.exists_relation_sum_zero_pos_coefficient_of_finrank_succ_lt_card hlt
    set w : ι → ℝ := fun i => fw ((L i).linear) with hw
    have hw1 : ∑ i ∈ t, w i = 0 := by
      rw [← htot, hT, Finset.sum_image hinj]
    have hw2 : ∑ i ∈ t, w i • (L i).linear = 0 := by
      rw [← hrel, hT, Finset.sum_image hinj]
    have hc : ∀ x, ∑ i ∈ t, w i * (L i) x = ∑ i ∈ t, w i * (L i) 0 := by
      intro x
      have hstep : ∀ i ∈ t, w i * (L i) x = w i * (L i).linear x + w i * (L i) 0 := by
        intro i _; rw [affine_decomp (L i) x]; ring
      rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
      have hzero : ∑ i ∈ t, w i * (L i).linear x = 0 := by
        have h := congrArg (fun g : (Fin n → ℝ) →ₗ[ℝ] ℝ => g x) hw2
        simpa [LinearMap.sum_apply] using h
      rw [hzero, zero_add]
    obtain ⟨i₀, hi₀t, hi₀eq⟩ := Finset.mem_image.1 hx₀T
    set A := t.filter (fun i => 0 < w i) with hA
    have hAsub : A ⊆ t := Finset.filter_subset _ _
    have hi₀A : i₀ ∈ A := by
      refine mem_filter.2 ⟨hi₀t, ?_⟩
      show (0:ℝ) < fw ((L i₀).linear)
      rw [hi₀eq]; exact hx₀pos
    have hAne : A.Nonempty := ⟨i₀, hi₀A⟩
    have hBne : (t \ A).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hAt : A = t := by
        apply Finset.Subset.antisymm hAsub
        intro i hi
        by_contra hni
        exact absurd (mem_sdiff.2 ⟨hi, hni⟩) (by simp [hempty])
      have hpos : 0 < ∑ i ∈ t, w i := by
        rw [← hAt]
        exact Finset.sum_pos (fun i hi => (mem_filter.1 hi).2) ⟨i₀, hi₀A⟩
      rw [hw1] at hpos
      exact lt_irrefl 0 hpos
    set P := ∑ i ∈ A, w i with hPdef
    have hP : 0 < P := Finset.sum_pos (fun i hi => (mem_filter.1 hi).2) hAne
    have hPB : ∑ j ∈ t \ A, w j = -P := by
      have h := Finset.sum_sdiff (f := w) hAsub
      rw [hw1] at h
      linarith [h]
    have hBneg : ∀ j ∈ t \ A, w j ≤ 0 := by
      intro j hj
      have hjt : j ∈ t := (mem_sdiff.1 hj).1
      have hjA : j ∉ A := (mem_sdiff.1 hj).2
      by_contra hpos
      exact hjA (mem_filter.2 ⟨hjt, not_le.1 hpos⟩)
    by_cases hcsign : ∑ i ∈ t, w i * (L i) 0 ≤ 0
    · refine ⟨A, hAsub, hAne, hBne, fun x => ?_⟩
      obtain ⟨i₁, hi₁, hi₁eq⟩ := Finset.exists_mem_eq_inf' hAne (fun i => L i x)
      obtain ⟨j₁, hj₁, hj₁eq⟩ := Finset.exists_mem_eq_sup' hBne (fun i => L i x)
      refine ⟨i₁, hi₁, j₁, hj₁, ?_⟩
      have h1 : P * (A.inf' hAne (fun i => L i x)) ≤ ∑ i ∈ A, w i * (L i) x := by
        rw [hPdef, Finset.sum_mul]
        refine Finset.sum_le_sum fun i hi => ?_
        exact mul_le_mul_of_nonneg_left (Finset.inf'_le (fun i => L i x) hi)
          (le_of_lt (mem_filter.1 hi).2)
      have h2 : (-P) * ((t \ A).sup' hBne (fun i => L i x)) ≤ ∑ j ∈ t \ A, w j * (L j) x := by
        rw [← hPB, Finset.sum_mul]
        refine Finset.sum_le_sum fun j hj => ?_
        exact mul_le_mul_of_nonpos_left (Finset.le_sup' (fun i => L i x) hj) (hBneg j hj)
      have h3 : ∑ i ∈ A, w i * (L i) x + ∑ j ∈ t \ A, w j * (L j) x
          = ∑ i ∈ t, w i * (L i) x := by
        rw [add_comm]; exact Finset.sum_sdiff hAsub
      rw [hc x] at h3
      nlinarith [h1, h2, h3, hcsign, hP, hi₁eq, hj₁eq]
    · push_neg at hcsign
      refine ⟨t \ A, Finset.sdiff_subset, hBne, ?_, fun x => ?_⟩
      · rwa [Finset.sdiff_sdiff_eq_self hAsub]
      · rw [Finset.sdiff_sdiff_eq_self hAsub]
        obtain ⟨j₁, hj₁, hj₁eq⟩ := Finset.exists_mem_eq_inf' hBne (fun i => L i x)
        obtain ⟨i₁, hi₁, hi₁eq⟩ := Finset.exists_mem_eq_sup' hAne (fun i => L i x)
        refine ⟨j₁, hj₁, i₁, hi₁, ?_⟩
        have h1 : ∑ i ∈ A, w i * (L i) x ≤ P * (A.sup' hAne (fun i => L i x)) := by
          rw [hPdef, Finset.sum_mul]
          refine Finset.sum_le_sum fun i hi => ?_
          exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun i => L i x) hi)
            (le_of_lt (mem_filter.1 hi).2)
        have h2 : ∑ j ∈ t \ A, w j * (L j) x ≤ (-P) * ((t \ A).inf' hBne (fun i => L i x)) := by
          rw [← hPB, Finset.sum_mul]
          refine Finset.sum_le_sum fun j hj => ?_
          exact mul_le_mul_of_nonpos_left (Finset.inf'_le (fun i => L i x) hj) (hBneg j hj)
        have h3 : ∑ i ∈ A, w i * (L i) x + ∑ j ∈ t \ A, w j * (L j) x
            = ∑ i ∈ t, w i * (L i) x := by
          rw [add_comm]; exact Finset.sum_sdiff hAsub
        rw [hc x] at h3
        nlinarith [h1, h2, h3, hcsign, hP, hi₁eq, hj₁eq]

/-! ### The height-reduction induction -/

private theorem isHH_mx (L : ι → ((Fin n → ℝ) →ᵃ[ℝ] ℝ)) [DecidableEq ι] :
    ∀ (N : ℕ) (t : Finset ι), t.card ≤ N → t.Nonempty → IsHH (mx L t) := by
  classical
  intro N
  induction N with
  | zero =>
      intro t hcard ht
      exact absurd hcard (by simpa using Nat.not_le.2 (Finset.card_pos.mpr ht))
  | succ N ih =>
      intro t hcard ht
      by_cases hsmall : t.card ≤ n + 1
      · exact isHH_mx_small L t ht hsmall
      · obtain ⟨A, hAt, hAne, hBne, hkey⟩ := split L t (by omega)
        -- every strictly smaller sub-maximum is `IsHH`
        have hsub : ∀ U ∈ A.powerset.erase ∅, IsHH (mx L (t \ U)) := by
          intro U hU
          have hUne : U.Nonempty := by
            rcases Finset.eq_empty_or_nonempty U with rfl | h
            · exact absurd rfl (Finset.ne_of_mem_erase hU)
            · exact h
          have hUA : U ⊆ A := Finset.mem_powerset.1 (Finset.mem_of_mem_erase hU)
          have hUt : U ⊆ t := hUA.trans hAt
          have hne : (t \ U).Nonempty := by
            obtain ⟨j, hj⟩ := hBne
            exact ⟨j, mem_sdiff.2 ⟨(mem_sdiff.1 hj).1,
              fun hjU => (mem_sdiff.1 hj).2 (hUA hjU)⟩⟩
          have hlt : (t \ U).card < t.card := by
            obtain ⟨u, hu⟩ := hUne
            refine Finset.card_lt_card
              ((Finset.ssubset_iff_of_subset Finset.sdiff_subset).2 ⟨u, hUt hu, ?_⟩)
            intro hcon
            exact (mem_sdiff.1 hcon).2 hu
          exact ih (t \ U) (by omega) hne
        -- the alternating identity
        have hdrop : ∀ (x : Fin n → ℝ) (i₀ : ι), i₀ ∈ A →
            (∀ i ∈ A, L i₀ x ≤ L i x) → ∀ V ⊆ A.erase i₀,
            mx L ((t \ V).erase i₀) x = mx L (t \ V) x := by
          intro x i₀ hi₀A hi₀min V hV
          have hVA : V ⊆ A := hV.trans (Finset.erase_subset _ _)
          have hBsub : ∀ j ∈ t \ A, j ∈ (t \ V).erase i₀ := by
            intro j hj
            have hjt : j ∈ t := (mem_sdiff.1 hj).1
            have hjA : j ∉ A := (mem_sdiff.1 hj).2
            refine Finset.mem_erase.2 ⟨fun hji => hjA (hji ▸ hi₀A), ?_⟩
            exact mem_sdiff.2 ⟨hjt, fun hjV => hjA (hVA hjV)⟩
          obtain ⟨jb, hjb⟩ := hBne
          have hEne : ((t \ V).erase i₀).Nonempty := ⟨jb, hBsub jb hjb⟩
          have hFne : (t \ V).Nonempty :=
            ⟨jb, mem_sdiff.2 ⟨(mem_sdiff.1 hjb).1, fun hjV => (mem_sdiff.1 hjb).2 (hVA hjV)⟩⟩
          rw [mx_eq L hEne x, mx_eq L hFne x]
          apply le_antisymm
          · exact Finset.sup'_le _ _ fun j hj =>
              Finset.le_sup' (fun i => L i x) (Finset.mem_of_mem_erase hj)
          · refine Finset.sup'_le _ _ fun j hj => ?_
            by_cases hji : j = i₀
            · rw [hji]
              obtain ⟨i₂, hi₂A, j₂, hj₂B, hij⟩ := hkey x
              calc L i₀ x ≤ L i₂ x := hi₀min i₂ hi₂A
                _ ≤ L j₂ x := hij
                _ ≤ ((t \ V).erase i₀).sup' hEne (fun i => L i x) :=
                    Finset.le_sup' (fun i => L i x) (hBsub j₂ hj₂B)
            · exact Finset.le_sup' (fun i => L i x) (Finset.mem_erase.2 ⟨hji, hj⟩)
        have hident : ∀ x, mx L t x
            = ∑ U ∈ A.powerset.erase ∅, ((-1 : ℝ) ^ (U.card + 1)) * mx L (t \ U) x := by
          intro x
          obtain ⟨i₀, hi₀A, hi₀min⟩ := Finset.exists_min_image A (fun i => L i x) hAne
          have hzero : ∑ U ∈ A.powerset, ((-1 : ℝ) ^ (U.card + 1)) * mx L (t \ U) x = 0 := by
            have hAins : A = insert i₀ (A.erase i₀) := (Finset.insert_erase hi₀A).symm
            rw [hAins, Finset.sum_powerset_insert (Finset.notMem_erase i₀ A),
              ← Finset.sum_add_distrib]
            refine Finset.sum_eq_zero fun V hV => ?_
            have hVsub : V ⊆ A.erase i₀ := Finset.mem_powerset.1 hV
            have hi₀V : i₀ ∉ V := fun h => (Finset.notMem_erase i₀ A) (hVsub h)
            have hcard' : (insert i₀ V).card = V.card + 1 := Finset.card_insert_of_notMem hi₀V
            have hset : t \ insert i₀ V = (t \ V).erase i₀ := Finset.sdiff_insert t V i₀
            rw [hcard', hset, hdrop x i₀ hi₀A hi₀min V hVsub, pow_succ]
            ring
          have hmem0 : (∅ : Finset ι) ∈ A.powerset := Finset.empty_mem_powerset A
          have hsplit :
              ((-1 : ℝ) ^ ((∅ : Finset ι).card + 1)) * mx L (t \ (∅ : Finset ι)) x
                + ∑ U ∈ A.powerset.erase ∅, ((-1 : ℝ) ^ (U.card + 1)) * mx L (t \ U) x
              = ∑ U ∈ A.powerset, ((-1 : ℝ) ^ (U.card + 1)) * mx L (t \ U) x :=
            Finset.add_sum_erase A.powerset
              (fun U => ((-1 : ℝ) ^ (U.card + 1)) * mx L (t \ U) x) hmem0
          rw [hzero] at hsplit
          simp only [Finset.card_empty, Finset.sdiff_empty, zero_add, pow_one] at hsplit
          linarith
        have hterm : ∀ U ∈ A.powerset.erase ∅,
            IsHH (fun x => ((-1 : ℝ) ^ (U.card + 1)) * mx L (t \ U) x) := by
          intro U hU
          have h := hsub U hU
          rcases Nat.even_or_odd (U.card + 1) with he | ho
          · rw [he.neg_one_pow]
            simpa using h
          · rw [ho.neg_one_pow]
            have h2 := isHH_neg h
            have heq : (fun x => (-1 : ℝ) * mx L (t \ U) x) = -(mx L (t \ U)) := by
              funext x; simp
            rw [heq]; exact h2
        have := isHH_sum (A.powerset.erase ∅)
          (fun U => fun x => ((-1 : ℝ) ^ (U.card + 1)) * mx L (t \ U) x) hterm
        rw [funext hident]
        exact this

end WSHR

theorem solution {m : ℕ} (L : Fin (m + 1) → ((Fin n → ℝ) →ᵃ[ℝ] ℝ)) :
    IsHH (fun x => (univ : Finset (Fin (m + 1))).sup' univ_nonempty fun i => L i x) := by
  classical
  have hne : (univ : Finset (Fin (m + 1))).Nonempty := univ_nonempty
  have h := WSHR.isHH_mx L (univ : Finset (Fin (m + 1))).card
    (univ : Finset (Fin (m + 1))) le_rfl hne
  have heq : WSHR.mx L (univ : Finset (Fin (m + 1)))
      = fun x => (univ : Finset (Fin (m + 1))).sup' univ_nonempty fun i => L i x := by
    funext x
    exact WSHR.mx_eq L hne x
  rwa [heq] at h
