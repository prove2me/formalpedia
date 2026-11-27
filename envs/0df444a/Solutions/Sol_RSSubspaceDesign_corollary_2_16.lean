-- Prove2me | solution 1 for RSSubspaceDesign.corollary_2_16
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:51:14.087497+00:00
-- url     : https://prove2.me/submissions/fcc300cd-3550-46ca-bc65-77828bb5e1d7

import Mathlib
import Definitions.Def_RSSubspaceDesign_ratFuncAlgebra

open Polynomial

namespace RSSubspaceDesign

theorem c216_key {K F : Type*} [Field K] [Field F] [Algebra K F] (p : K[X]) :
    letI := ratFuncAlgebra K F
    algebraMap (RatFunc K) (RatFunc F) (algebraMap K[X] (RatFunc K) p) =
      algebraMap F[X] (RatFunc F) (p.map (algebraMap K F)) := by
  have h := RatFunc.map_apply_div (Polynomial.mapRingHom (algebraMap K F))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap K F).injective)) p 1
  simp only [map_one, div_one] at h
  exact h

theorem c216_key' {K F : Type*} [Field K] [Field F] [Algebra K F] (p : K[X]) (x : RatFunc F) :
    letI := ratFuncAlgebra K F
    (algebraMap K[X] (RatFunc K) p) • x =
      algebraMap F[X] (RatFunc F) (p.map (algebraMap K F)) * x := by
  letI := ratFuncAlgebra K F
  rw [Algebra.smul_def, c216_key]

theorem c216_pigeon {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F] (q : F[X])
    (hq : q ≠ 0) : ∃ c : K[X], c ≠ 0 ∧ q ∣ c.map (algebraMap K F) := by
  have : Module.Finite F (AdjoinRoot q) := (AdjoinRoot.powerBasis hq).finite
  have : Finite (AdjoinRoot q) := Module.finite_of_finite F
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => AdjoinRoot.mk q (X ^ n))
  refine ⟨X ^ i - X ^ j, ?_, ?_⟩
  · intro h0
    have := congrArg (fun p => Polynomial.coeff p i) h0
    simp [coeff_X_pow, hij] at this
  · simp only [Polynomial.map_sub, Polynomial.map_pow, map_X]
    exact AdjoinRoot.mk_eq_mk.mp h


theorem c216_pd {K F : Type*} [Field K] [Field F] [Algebra K F] {ι : Type*} [Fintype ι]
    (a : ι → F[X]) (hli : LinearIndependent K (fun i => (a i).leadingCoeff)) (c : ι → K[X]) :
    (∑ i, (c i).map (algebraMap K F) * a i).degree =
      Finset.univ.sup fun i => (a i).degree + (c i).degree := by
  have hterm : ∀ i, ((c i).map (algebraMap K F) * a i).degree = (a i).degree + (c i).degree := by
    intro i; rw [degree_mul, degree_map, add_comm]
  apply le_antisymm
  · refine (degree_sum_le _ _).trans (le_of_eq ?_)
    simp only [hterm]
  · generalize hD : (Finset.univ.sup fun i => (a i).degree + (c i).degree) = D
    induction D using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe n =>
      apply le_degree_of_ne_zero
      rw [finsetSum_coeff]
      classical
      let κ : ι → K := fun i => if (a i).degree + (c i).degree = n then (c i).leadingCoeff else 0
      have hcoef : ∀ i, ((c i).map (algebraMap K F) * a i).coeff n = κ i • (a i).leadingCoeff := by
        intro i
        by_cases h : (a i).degree + (c i).degree = n
        · have h1 : ((c i).map (algebraMap K F) * a i).natDegree = n :=
            natDegree_eq_of_degree_eq_some (by rw [hterm, h])
          simp only [κ, if_pos h]
          rw [← h1, coeff_natDegree, leadingCoeff_mul, leadingCoeff_map, Algebra.smul_def]
        · simp only [κ, if_neg h, zero_smul]
          apply coeff_eq_zero_of_degree_lt
          rw [hterm]
          refine lt_of_le_of_ne ?_ h
          have := Finset.le_sup (f := fun i => (a i).degree + (c i).degree) (Finset.mem_univ i)
          rw [hD] at this
          exact this
      simp only [hcoef]
      intro h0
      have hall := Fintype.linearIndependent_iff.mp hli κ h0
      have hne : (Finset.univ : Finset ι).Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne, Finset.sup_empty] at hD
        exact WithBot.bot_ne_coe hD
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup _ hne (fun i => (a i).degree + (c i).degree)
      rw [hD] at hi
      have hci : c i ≠ 0 := by
        rintro hc
        rw [hc, degree_zero, WithBot.add_bot] at hi
        exact WithBot.bot_ne_coe hi.symm
      have : (c i).leadingCoeff = 0 := by
        have := hall i
        simp only [κ] at this
        exact (ite_eq_right_iff.mp this) hi.symm
      exact hci (leadingCoeff_eq_zero.mp this)

theorem c216_indep {K F : Type*} [Field K] [Field F] [Algebra K F] {ι : Type*} [Fintype ι]
    (a : ι → F[X]) (hli : LinearIndependent K (fun i => (a i).leadingCoeff)) (c : ι → K[X])
    (h0 : ∑ i, (c i).map (algebraMap K F) * a i = 0) : c = 0 := by
  have h := c216_pd a hli c
  rw [h0, degree_zero, eq_comm, Finset.sup_eq_bot_iff] at h
  funext i
  have hai : a i ≠ 0 := by
    intro ha
    have := hli.ne_zero i
    simp [ha] at this
  rcases WithBot.add_eq_bot.mp (h i (Finset.mem_univ i)) with h1 | h1
  · exact absurd (degree_eq_bot.mp h1) hai
  · exact degree_eq_bot.mp h1


theorem c216_span {K F : Type*} [Field K] [Field F] [Algebra K F] {ι : Type*} [Fintype ι]
    (a : ι → F[X]) (P : F[X] → Prop)
    (hsub : ∀ u (c : ι → K[X]), P u → P (u - ∑ i, (c i).map (algebraMap K F) * a i))
    (h2 : ∀ u, P u → u ≠ 0 → ∃ κ : ι → K, (∀ i, κ i ≠ 0 → (a i).natDegree ≤ u.natDegree) ∧
      u.leadingCoeff = ∑ i, κ i • (a i).leadingCoeff) :
    ∀ u, P u → ∃ c : ι → K[X], u = ∑ i, (c i).map (algebraMap K F) * a i := by
  intro u
  refine Polynomial.degree_lt_wf.induction
    (C := fun u => P u → ∃ c : ι → K[X], u = ∑ i, (c i).map (algebraMap K F) * a i) u ?_
  intro u ih hu
  by_cases hu0 : u = 0
  · exact ⟨0, by simp [hu0]⟩
  obtain ⟨κ, hκ, hlc⟩ := h2 u hu hu0
  set n := u.natDegree with hn
  let c0 : ι → K[X] := fun i => C (κ i) * X ^ (n - (a i).natDegree)
  have hmap : ∀ i, (c0 i).map (algebraMap K F) * a i =
      C (algebraMap K F (κ i)) * (X ^ (n - (a i).natDegree) * a i) := by
    intro i
    simp only [c0, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, mul_assoc]
  set q := ∑ i, (c0 i).map (algebraMap K F) * a i with hq
  have hq_le : q.degree ≤ n := by
    refine (degree_sum_le _ _).trans (Finset.sup_le fun i _ => ?_)
    rw [hmap]
    by_cases hk : κ i = 0
    · simp [hk]
    · have hd := hκ i hk
      refine degree_le_of_natDegree_le ?_
      refine (natDegree_C_mul_le _ _).trans ?_
      refine (natDegree_mul_le).trans ?_
      have := natDegree_X_pow_le (R := F) (n - (a i).natDegree)
      omega
  have hq_coeff : q.coeff n = u.leadingCoeff := by
    rw [hq, finsetSum_coeff, hlc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hmap]
    by_cases hk : κ i = 0
    · simp [hk]
    · have hd := hκ i hk
      rw [coeff_C_mul, coeff_X_pow_mul', if_pos (Nat.sub_le _ _), Algebra.smul_def]
      congr 2
      omega
  have hu_deg : u.degree = n := degree_eq_natDegree hu0
  have hq_deg : q.degree = n := by
    refine le_antisymm hq_le (le_degree_of_ne_zero ?_)
    rw [hq_coeff]
    exact leadingCoeff_ne_zero.mpr hu0
  have hq_lc : q.leadingCoeff = u.leadingCoeff := by
    rw [leadingCoeff, natDegree_eq_of_degree_eq_some hq_deg, hq_coeff]
  have hdeg : (u - q).degree < u.degree :=
    degree_sub_lt_left (by rw [hu_deg, hq_deg]) hu0 hq_lc.symm
  obtain ⟨c', hc'⟩ := ih (u - q) hdeg (hsub u c0 hu)
  refine ⟨fun i => c' i + c0 i, ?_⟩
  simp only [Polynomial.map_add, add_mul, Finset.sum_add_distrib, ← hc', hq]
  ring


theorem c216_exists {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F]
    (P : F[X] → Prop) :
    ∃ T : Finset F[X], (∀ t ∈ T, P t) ∧ LinearIndepOn K Polynomial.leadingCoeff (T : Set F[X]) ∧
      ∀ u, P u → u ≠ 0 → ∃ κ : F[X] → K, (∀ t ∈ T, κ t ≠ 0 → t.natDegree ≤ u.natDegree) ∧
        u.leadingCoeff = ∑ t ∈ T, κ t • t.leadingCoeff := by
  classical
  have : Fintype F := Fintype.ofFinite F
  let G : Finset F[X] → Prop := fun T =>
    (∀ t ∈ T, P t) ∧ LinearIndepOn K Polynomial.leadingCoeff (T : Set F[X])
  have hcard : ∀ T, G T → T.card ≤ Fintype.card F := by
    intro T hT
    have := Finset.card_le_card_of_injOn _ (fun x _ => Finset.mem_univ (Polynomial.leadingCoeff x))
      hT.2.injOn
    simpa using this
  let m := Nat.findGreatest (fun n => ∃ T, G T ∧ T.card = n) (Fintype.card F)
  have hm : ∃ T, G T ∧ T.card = m :=
    Nat.findGreatest_spec (P := fun n => ∃ T, G T ∧ T.card = n) (Nat.zero_le _)
      ⟨∅, ⟨by simp, by simp [linearIndepOn_empty]⟩, rfl⟩
  have hmax : ∀ T, G T → T.card ≤ m := fun T hT =>
    Nat.le_findGreatest (P := fun n => ∃ T, G T ∧ T.card = n) (hcard T hT) ⟨T, hT, rfl⟩
  have hex : ∃ s, ∃ T, G T ∧ T.card = m ∧ ∑ t ∈ T, t.natDegree = s := by
    obtain ⟨T, hT, hc⟩ := hm; exact ⟨_, T, hT, hc, rfl⟩
  obtain ⟨T, hT, hTc, hTs⟩ := Nat.find_spec hex
  have hmin : ∀ T', G T' → T'.card = m → Nat.find hex ≤ ∑ t ∈ T', t.natDegree :=
    fun T' h1 h2 => Nat.find_min' hex ⟨T', h1, h2, rfl⟩
  refine ⟨T, hT.1, hT.2, ?_⟩
  intro u hu hu0
  by_contra hcon
  by_cases hspan : u.leadingCoeff ∈ Submodule.span K (Polynomial.leadingCoeff '' (T : Set F[X]))
  · obtain ⟨l, hl, hlu⟩ := (Finsupp.mem_span_image_iff_linearCombination K).mp hspan
    have hsum : Finsupp.linearCombination K Polynomial.leadingCoeff l =
        ∑ t ∈ T, l t • t.leadingCoeff := by
      rw [Finsupp.linearCombination_apply]
      exact Finsupp.sum_of_support_subset l
        (by exact_mod_cast (Finsupp.mem_supported _ _).mp hl) _ (by simp)
    by_cases hall : ∀ t ∈ T, l t ≠ 0 → t.natDegree ≤ u.natDegree
    · exact hcon ⟨l, hall, by rw [← hlu, hsum]⟩
    push Not at hall
    obtain ⟨t0, ht0, hl0, hdeg⟩ := hall
    have hnot : u.leadingCoeff ∉ Submodule.span K
        (Polynomial.leadingCoeff '' ((T.erase t0 : Finset F[X]) : Set F[X])) := by
      intro h'
      obtain ⟨l', hl', hlu'⟩ := (Finsupp.mem_span_image_iff_linearCombination K).mp h'
      have h1 : l - l' ∈ Finsupp.supported K K (T : Set F[X]) :=
        Submodule.sub_mem _ hl (Finsupp.supported_mono (by simp [Finset.coe_erase]) hl')
      have h2 := linearIndepOn_iff.mp hT.2 (l - l') h1 (by rw [map_sub, hlu, hlu', sub_self])
      have h3 : l' t0 = 0 := (Finsupp.mem_supported' _ _).mp hl' t0 (by simp)
      apply hl0
      rw [sub_eq_zero] at h2
      rw [h2, h3]
    have huT : u ∉ T.erase t0 := fun h =>
      hnot (Submodule.subset_span (Set.mem_image_of_mem _ (by exact_mod_cast h)))
    have hG : G (insert u (T.erase t0)) := by
      refine ⟨?_, ?_⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact hu
        · exact hT.1 t (Finset.mem_of_mem_erase ht)
      · rw [Finset.coe_insert, linearIndepOn_insert (by exact_mod_cast huT)]
        exact ⟨hT.2.mono (by simp), hnot⟩
    have hc : (insert u (T.erase t0)).card = m := by
      rw [Finset.card_insert_of_notMem huT, Finset.card_erase_of_mem ht0, ← hTc]
      have := Finset.card_pos.mpr ⟨t0, ht0⟩
      omega
    have := hmin _ hG hc
    rw [Finset.sum_insert huT, ← hTs] at this
    have h4 := Finset.add_sum_erase T (fun t => t.natDegree) ht0
    omega
  · have huT : u ∉ T := fun h => hspan (Submodule.subset_span (Set.mem_image_of_mem _ h))
    have hG : G (insert u T) := by
      refine ⟨?_, ?_⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact hu
        · exact hT.1 t ht
      · rw [Finset.coe_insert, linearIndepOn_insert (by exact_mod_cast huT)]
        exact ⟨hT.2, hspan⟩
    have := hmax _ hG
    rw [Finset.card_insert_of_notMem huT] at this
    omega


theorem c216_ident {K F : Type*} [Field K] [Field F] [Algebra K F] {ι : Type*} [Fintype ι]
    (a : ι → F[X]) (c : ι → K[X]) :
    letI := ratFuncAlgebra K F
    algebraMap F[X] (RatFunc F) (∑ i, (c i).map (algebraMap K F) * a i) =
      ∑ i, algebraMap K[X] (RatFunc K) (c i) • algebraMap F[X] (RatFunc F) (a i) := by
  letI := ratFuncAlgebra K F
  simp only [map_sum, map_mul, c216_key']

end RSSubspaceDesign

open RSSubspaceDesign in
theorem solution {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F] (d : ℕ) :
    letI := ratFuncAlgebra K F
    ∀ A : Submodule (RatFunc K) (RatFunc F), Module.finrank (RatFunc K) A = d →
      ∃ a : Fin d → F[X],
        (∀ i, algebraMap F[X] (RatFunc F) (a i) ∈ A) ∧
        (∀ c : Fin d → K[X], ∑ i, (c i).map (algebraMap K F) * a i = 0 → c = 0) ∧
        (∀ u : F[X], algebraMap F[X] (RatFunc F) u ∈ A →
          ∃ c : Fin d → K[X], u = ∑ i, (c i).map (algebraMap K F) * a i) ∧
        (∀ c : Fin d → K[X], (∑ i, (c i).map (algebraMap K F) * a i).degree =
          Finset.univ.sup fun i => (a i).degree + (c i).degree) ∧
        ∀ k : ℕ, ∀ u : F[X],
          (algebraMap F[X] (RatFunc F) u ∈ A ∧ u.degree < k) ↔
            ∃ c : Fin d → K[X], (∀ i, (c i).degree + (a i).degree < k) ∧
              u = ∑ i, (c i).map (algebraMap K F) * a i := by
  letI := ratFuncAlgebra K F
  intro A hA
  classical
  obtain ⟨T, hTP, hTli, hT2⟩ :=
    c216_exists (K := K) (fun u : F[X] => algebraMap F[X] (RatFunc F) u ∈ A)
  let e : Fin T.card ≃ T := T.equivFin.symm
  let a : Fin T.card → F[X] := fun i => (e i).1
  have ha : ∀ i, algebraMap F[X] (RatFunc F) (a i) ∈ A := fun i => hTP _ (e i).2
  have hli : LinearIndependent K (fun i => (a i).leadingCoeff) :=
    hTli.comp (fun i => e i) e.injective
  have hmem : ∀ c : Fin T.card → K[X],
      algebraMap F[X] (RatFunc F) (∑ i, (c i).map (algebraMap K F) * a i) ∈ A := by
    intro c
    rw [c216_ident]
    exact A.sum_mem fun i _ => A.smul_mem _ (ha i)
  have hsub : ∀ u (c : Fin T.card → K[X]), algebraMap F[X] (RatFunc F) u ∈ A →
      algebraMap F[X] (RatFunc F) (u - ∑ i, (c i).map (algebraMap K F) * a i) ∈ A := by
    intro u c hu
    rw [map_sub]
    exact A.sub_mem hu (hmem c)
  have h2 : ∀ u, algebraMap F[X] (RatFunc F) u ∈ A → u ≠ 0 → ∃ κ : Fin T.card → K,
      (∀ i, κ i ≠ 0 → (a i).natDegree ≤ u.natDegree) ∧
      u.leadingCoeff = ∑ i, κ i • (a i).leadingCoeff := by
    intro u hu hu0
    obtain ⟨κ, hκ, hlc⟩ := hT2 u hu hu0
    refine ⟨fun i => κ (a i), fun i hi => hκ _ (e i).2 hi, ?_⟩
    rw [hlc, ← Finset.sum_coe_sort T]
    exact (e.sum_comp (fun t => κ t • (t : F[X]).leadingCoeff)).symm
  have hspan := c216_span a _ hsub h2
  -- L-independence
  have hLi : LinearIndependent (RatFunc K) (fun i => algebraMap F[X] (RatFunc F) (a i)) := by
    rw [Fintype.linearIndependent_iff]
    intro r hr i
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors K[X])
      (Finset.univ : Finset (Fin T.card)) r
    choose p hp using fun i => hb i (Finset.mem_univ i)
    have hb0 : algebraMap K[X] (RatFunc K) (b : K[X]) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr
        (nonZeroDivisors.ne_zero b.2)
    have hsum : algebraMap F[X] (RatFunc F) (∑ i, (p i).map (algebraMap K F) * a i) = 0 := by
      have hp' : ∀ i, algebraMap K[X] (RatFunc K) (p i) =
          algebraMap K[X] (RatFunc K) (b : K[X]) * r i := fun i => by
        rw [hp, Algebra.smul_def]
      rw [c216_ident]
      simp only [hp', mul_smul]
      rw [← Finset.smul_sum, hr, smul_zero]
    rw [map_eq_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))] at hsum
    have hp0 := c216_indep a hli p hsum
    have := hp i
    rw [hp0, Pi.zero_apply, map_zero, Algebra.smul_def, eq_comm, mul_eq_zero] at this
    exact this.resolve_left hb0
  -- L-span
  have hLs : A ≤ Submodule.span (RatFunc K)
      (Set.range fun i => algebraMap F[X] (RatFunc F) (a i)) := by
    intro x hx
    obtain ⟨c, hc0, q', hq'⟩ := c216_pigeon (K := K) x.denom x.denom_ne_zero
    have hne : algebraMap K[X] (RatFunc K) c ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hc0
    have hden : algebraMap F[X] (RatFunc F) x.denom ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mpr x.denom_ne_zero
    have hux : algebraMap F[X] (RatFunc F) (x.num * q') = algebraMap K[X] (RatFunc K) c • x := by
      have h1 : algebraMap F[X] (RatFunc F) x.num = x * algebraMap F[X] (RatFunc F) x.denom :=
        (div_eq_iff hden).mp (RatFunc.num_div_denom x)
      rw [c216_key', hq', map_mul, map_mul, h1]
      ring
    have hu : algebraMap F[X] (RatFunc F) (x.num * q') ∈ A := by
      rw [hux]; exact A.smul_mem _ hx
    obtain ⟨cc, hcc⟩ := hspan _ hu
    have hin : algebraMap F[X] (RatFunc F) (x.num * q') ∈ Submodule.span (RatFunc K)
        (Set.range fun i => algebraMap F[X] (RatFunc F) (a i)) := by
      rw [hcc, c216_ident]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
    have hx' : x = (algebraMap K[X] (RatFunc K) c)⁻¹ •
        algebraMap F[X] (RatFunc F) (x.num * q') := by
      rw [hux, inv_smul_smul₀ hne]
    rw [hx']
    exact Submodule.smul_mem _ _ hin
  have hspanEq : Submodule.span (RatFunc K)
      (Set.range fun i => algebraMap F[X] (RatFunc F) (a i)) = A :=
    le_antisymm (Submodule.span_le.mpr (Set.range_subset_iff.mpr ha)) hLs
  have hcard := finrank_span_eq_card hLi
  rw [hspanEq, hA, Fintype.card_fin] at hcard
  subst hcard
  refine ⟨a, ha, fun c h0 => c216_indep a hli c h0, hspan, c216_pd a hli, ?_⟩
  intro k u
  constructor
  · rintro ⟨hu, hdeg⟩
    obtain ⟨c, rfl⟩ := hspan u hu
    refine ⟨c, fun i => ?_, rfl⟩
    rw [c216_pd a hli c] at hdeg
    have := (Finset.sup_lt_iff (WithBot.bot_lt_coe k)).mp hdeg i (Finset.mem_univ i)
    rwa [add_comm] at this
  · rintro ⟨c, hc, rfl⟩
    refine ⟨hmem c, ?_⟩
    rw [c216_pd a hli c]
    exact (Finset.sup_lt_iff (WithBot.bot_lt_coe k)).mpr fun i _ => by
      rw [add_comm]; exact hc i
