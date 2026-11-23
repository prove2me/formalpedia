-- Prove2me | solution 1 for SubmodMDP.Policies.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:38:34.173254+00:00
-- url     : https://prove2.me/submissions/89e640d2-f6fb-4263-9afa-44455ee3fd25

import Definitions.Def_SubmodMDP_Policies_GraphMDP

open SubmodMDP.Policies

namespace Lemma10Aux

noncomputable def stepWeight (M : GMDP) (π : GPolicy M) (w : List (Fin M.G.N))
    (v : Fin M.G.N) : ℝ :=
  match w.getLast? with
  | none => if v = M.s then 1 else 0
  | some u => if M.chance u then M.p u v else π w v

noncomputable def extSum (M : GMDP) (π : GPolicy M) :
    ℕ → List (Fin M.G.N) → (List (Fin M.G.N) → ℝ) → ℝ
  | 0, w, Φ => Φ w
  | m + 1, w, Φ => ∑ v : Fin M.G.N, stepWeight M π w v * extSum M π m (w ++ [v]) Φ

lemma extSum_zero_fn (M : GMDP) (π : GPolicy M) (m : ℕ) (w : List (Fin M.G.N)) :
    extSum M π m w (fun _ => 0) = 0 := by
  induction m generalizing w with
  | zero => rfl
  | succ m ih => simp [extSum, ih]

lemma extSum_mul_const (M : GMDP) (π : GPolicy M) (m : ℕ) (w : List (Fin M.G.N))
    (Φ : List (Fin M.G.N) → ℝ) (C : ℝ) :
    extSum M π m w (fun P => Φ P * C) = extSum M π m w Φ * C := by
  induction m generalizing w with
  | zero => rfl
  | succ m ih =>
    simp only [extSum, ih, Finset.sum_mul, mul_assoc]

lemma extSum_add (M : GMDP) (π : GPolicy M) (a b : ℕ) (w : List (Fin M.G.N))
    (Φ : List (Fin M.G.N) → ℝ) :
    extSum M π (a + b) w Φ = extSum M π a w (fun w' => extSum M π b w' Φ) := by
  induction a generalizing w with
  | zero => simp [extSum]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [extSum, ih]

lemma gstep_eq_stepWeight (M : GMDP) (π : GPolicy M) (τ : Fin M.G.H → Fin M.G.N)
    (j : Fin M.G.H) :
    gstep M π τ j = stepWeight M π ((List.ofFn τ).take j.val) (τ j) := by
  by_cases hj : j.val = 0
  · simp [gstep, stepWeight, hj]
  · have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj
    have hlen : ((List.ofFn τ).take j.val).length = j.val := by
      simp [Nat.le_of_lt j.isLt]
    have hlast : ((List.ofFn τ).take j.val).getLast? =
        some (τ ⟨j.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩) := by
      rw [List.getLast?_eq_getElem?, hlen]
      have hlt : j.val - 1 < ((List.ofFn τ).take j.val).length := by omega
      rw [List.getElem?_eq_getElem hlt]
      simp
    simp [gstep, stepWeight, hj, hlast]

lemma sum_prod_stepWeight_eq_extSum (M : GMDP) (π : GPolicy M) :
    ∀ (m : ℕ) (w : List (Fin M.G.N)) (Φ : List (Fin M.G.N) → ℝ),
      (∑ σ : Fin m → Fin M.G.N,
        (∏ j : Fin m, stepWeight M π (w ++ (List.ofFn σ).take j.val) (σ j)) *
          Φ (w ++ List.ofFn σ)) =
      extSum M π m w Φ
  | 0, w, Φ => by
    have huniq : (Finset.univ : Finset (Fin 0 → Fin M.G.N)) = {Fin.elim0} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      exact ⟨Finset.mem_univ _, fun σ _ => Subsingleton.elim σ Fin.elim0⟩
    rw [huniq, Finset.sum_singleton]
    simp [extSum]
  | m + 1, w, Φ => by
    have hequiv : (∑ σ : Fin (m + 1) → Fin M.G.N,
        (∏ j : Fin (m + 1), stepWeight M π (w ++ (List.ofFn σ).take j.val) (σ j)) *
          Φ (w ++ List.ofFn σ)) =
      ∑ p : Fin M.G.N × (Fin m → Fin M.G.N),
        (∏ j : Fin (m + 1), stepWeight M π
          (w ++ (List.ofFn (@Fin.cons m (fun _ => Fin M.G.N) p.1 p.2)).take j.val)
          (@Fin.cons m (fun _ => Fin M.G.N) p.1 p.2 j)) *
          Φ (w ++ List.ofFn (@Fin.cons m (fun _ => Fin M.G.N) p.1 p.2)) := by
      refine Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Fin M.G.N)).symm _ _ ?_
      intro σ
      simp [Fin.consEquiv_symm_apply]
    rw [hequiv, Fintype.sum_prod_type]
    simp only [extSum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← sum_prod_stepWeight_eq_extSum M π m (w ++ [v]) Φ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fin.prod_univ_succ]
    have h0 : stepWeight M π
        (w ++ (List.ofFn (@Fin.cons m (fun _ => Fin M.G.N) v σ)).take (0 : Fin (m + 1)).val)
        (@Fin.cons m (fun _ => Fin M.G.N) v σ 0) = stepWeight M π w v := by simp
    have hprod : (∏ i : Fin m,
        stepWeight M π
          (w ++ (List.ofFn (@Fin.cons m (fun _ => Fin M.G.N) v σ)).take (Fin.succ i).val)
          (@Fin.cons m (fun _ => Fin M.G.N) v σ (Fin.succ i))) =
        ∏ i : Fin m, stepWeight M π ((w ++ [v]) ++ (List.ofFn σ).take i.val) (σ i) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [List.ofFn_succ, List.take_succ_cons, List.append_assoc]
    have happ : w ++ List.ofFn (@Fin.cons m (fun _ => Fin M.G.N) v σ) =
        (w ++ [v]) ++ List.ofFn σ := by
      simp [List.ofFn_succ, List.append_assoc]
    rw [h0, hprod, happ, mul_assoc]

lemma image_univ_eq_toFinset_ofFn {m N : ℕ} (τ : Fin m → Fin N) :
    Finset.univ.image τ = (List.ofFn τ).toFinset := by
  ext v
  simp [List.mem_ofFn]

lemma visitMoment_eq_extSum (M : GMDP) (π : GPolicy M) (J : Finset (Fin M.G.N)) :
    visitMoment M π J = extSum M π M.G.H [] (fun P => liftInd P.toFinset J) := by
  unfold visitMoment gpathProb
  have h1 : ∀ τ : Fin M.G.H → Fin M.G.N,
      (∏ j : Fin M.G.H, gstep M π τ j) * liftInd (Finset.univ.image τ) J =
      (∏ j : Fin M.G.H, stepWeight M π ([] ++ (List.ofFn τ).take j.val) (τ j)) *
        liftInd ([] ++ List.ofFn τ).toFinset J := by
    intro τ
    rw [image_univ_eq_toFinset_ofFn]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    simpa using gstep_eq_stepWeight M π τ j
  simp_rw [h1]
  exact sum_prod_stepWeight_eq_extSum M π M.G.H [] (fun P => liftInd P.toFinset J)

def GoodPrefix (M : GMDP) (w : List (Fin M.G.N)) : Prop :=
  (w ≠ [] → IsWalkFromS M w) ∧ ∀ (k : ℕ) (hk : k < w.length), M.G.layer w[k] = k + 1

lemma goodPrefix_nil (M : GMDP) : GoodPrefix M [] :=
  ⟨fun h => (h rfl).elim, fun _ hk => by simp at hk⟩

lemma goodPrefix_snoc (M : GMDP) (hM : M.WF) (π : GPolicy M) (hπ : IsGPolicy M π)
    (w : List (Fin M.G.N)) (hw : GoodPrefix M w) (hlen : w.length < M.G.H)
    (v : Fin M.G.N) (hstep : stepWeight M π w v ≠ 0) :
    GoodPrefix M (w ++ [v]) := by
  cases w with
  | nil =>
    simp only [stepWeight, List.getLast?_nil] at hstep
    have hv : v = M.s := by
      by_contra hne
      simp [hne] at hstep
    subst hv
    refine ⟨fun _ => ⟨by simp, fun i hi => by simp at hi⟩, ?_⟩
    intro k hk
    simp only [List.nil_append, List.length_singleton] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    change M.G.layer M.s = 1
    exact (hM.2.1 M.s).mpr rfl
  | cons a tl =>
    set w0 := a :: tl
    have hw_ne : w0 ≠ [] := List.cons_ne_nil a tl
    have hwalk : IsWalkFromS M w0 := hw.1 hw_ne
    have hlast_idx : w0.length - 1 < w0.length := by simp [w0]
    set u := w0[w0.length - 1]
    have hlast : w0.getLast? = some u := by
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlast_idx]
    have hulay : M.G.layer u = w0.length := by
      have := hw.2 (w0.length - 1) hlast_idx
      dsimp [u]
      omega
    have harc : M.G.arc u v = true := by
      simp only [stepWeight, hlast] at hstep
      by_cases hc : M.chance u = true
      · simp only [hc, ↓reduceIte] at hstep
        exact ((hM.2.2.2 u hc).2.1 v).mp hstep
      · have hcf : M.chance u = false := Bool.eq_false_iff.mpr hc
        simp only [hcf, Bool.false_eq_true, ↓reduceIte] at hstep
        exact (hπ w0 hwalk hlen u hlast hcf).2.2 v hstep
    have hvlay : M.G.layer v = w0.length + 1 := by
      have := hM.1.2 u v harc
      omega
    refine ⟨fun _ => ?_, ?_⟩
    · refine ⟨by simpa [w0] using hwalk.1, ?_⟩
      intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hk_lt : k + 1 < w0.length
      · have hk_lt0 : k < w0.length := by omega
        simp [List.getElem_append_left hk_lt0, List.getElem_append_left hk_lt, hwalk.2 k hk_lt]
      · have hk_eq : k = w0.length - 1 := by omega
        subst hk_eq
        have h1 : (w0 ++ [v])[w0.length - 1] = u := List.getElem_append_left hlast_idx
        have h2 : (w0 ++ [v])[w0.length - 1 + 1] = v := by
          have heq : w0.length - 1 + 1 = w0.length := by omega
          simp [heq]
        rw [h1, h2]
        exact harc
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hk_lt : k < w0.length
      · rw [List.getElem_append_left hk_lt]
        exact hw.2 k hk_lt
      · have hk_eq : k = w0.length := by omega
        subst hk_eq
        simpa using hvlay

lemma sum_stepWeight_eq_one (M : GMDP) (hM : M.WF) (π : GPolicy M) (hπ : IsGPolicy M π)
    (w : List (Fin M.G.N)) (hw : GoodPrefix M w) (hlen : w.length < M.G.H) :
    ∑ v : Fin M.G.N, stepWeight M π w v = 1 := by
  cases w with
  | nil =>
    simp [stepWeight]
  | cons a tl =>
    set w0 := a :: tl
    have hw_ne : w0 ≠ [] := List.cons_ne_nil a tl
    have hwalk : IsWalkFromS M w0 := hw.1 hw_ne
    have hlast_idx : w0.length - 1 < w0.length := by simp [w0]
    set u := w0[w0.length - 1]
    have hlast : w0.getLast? = some u := by
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlast_idx]
    have hulay : M.G.layer u = w0.length := by
      have := hw.2 (w0.length - 1) hlast_idx
      dsimp [u]
      omega
    simp only [stepWeight, hlast]
    by_cases hc : M.chance u = true
    · simp only [hc, ↓reduceIte]
      exact (hM.2.2.2 u hc).2.2 (by omega)
    · have hcf : M.chance u = false := Bool.eq_false_iff.mpr hc
      simp only [hcf, Bool.false_eq_true, ↓reduceIte]
      exact (hπ w0 hwalk hlen u hlast hcf).2.1

lemma extSum_const_one (M : GMDP) (hM : M.WF) (π : GPolicy M) (hπ : IsGPolicy M π) :
    ∀ (m : ℕ) (w : List (Fin M.G.N)), GoodPrefix M w → w.length + m ≤ M.G.H →
      extSum M π m w (fun _ => 1) = 1
  | 0, _, _, _ => rfl
  | m + 1, w, hw, hlen => by
    simp only [extSum]
    have hcongr : ∀ v : Fin M.G.N,
        stepWeight M π w v * extSum M π m (w ++ [v]) (fun _ => 1) = stepWeight M π w v := by
      intro v
      by_cases hv : stepWeight M π w v = 0
      · simp [hv]
      · have hw' := goodPrefix_snoc M hM π hπ w hw (by omega) v hv
        rw [extSum_const_one M hM π hπ m (w ++ [v]) hw' (by simp; omega), mul_one]
    simp_rw [hcongr]
    exact sum_stepWeight_eq_one M hM π hπ w hw (by omega)

lemma extSum_congr_good (M : GMDP) (hM : M.WF) (π : GPolicy M) (hπ : IsGPolicy M π) :
    ∀ (m : ℕ) (w : List (Fin M.G.N)), GoodPrefix M w → w.length + m ≤ M.G.H →
      ∀ {Φ Ψ : List (Fin M.G.N) → ℝ},
      (∀ sfx : List (Fin M.G.N), sfx.length = m → GoodPrefix M (w ++ sfx) →
        Φ (w ++ sfx) = Ψ (w ++ sfx)) →
      extSum M π m w Φ = extSum M π m w Ψ
  | 0, w, hw, _, Φ, Ψ, hfg => by
    simp only [extSum]
    simpa using hfg [] rfl (by simpa using hw)
  | m + 1, w, hw, hlen, Φ, Ψ, hfg => by
    simp only [extSum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : stepWeight M π w v = 0
    · simp [hv]
    · have hw' := goodPrefix_snoc M hM π hπ w hw (by omega) v hv
      congr 1
      exact extSum_congr_good M hM π hπ m (w ++ [v]) hw' (by simp; omega) (fun sfx hsfx hgood => by
        have hassoc : (w ++ [v]) ++ sfx = w ++ (v :: sfx) := by simp [List.append_assoc]
        rw [hassoc] at hgood ⊢
        exact hfg (v :: sfx) (by simp [hsfx]) hgood)

lemma subset_append_iff_of_layer_le (M : GMDP) (w₁ sfx : List (Fin M.G.N))
    (hw : GoodPrefix M (w₁ ++ sfx)) (I : Finset (Fin M.G.N))
    (hIlay : ∀ v ∈ I, M.G.layer v ≤ w₁.length) :
    I ⊆ (w₁ ++ sfx).toFinset ↔ I ⊆ w₁.toFinset := by
  constructor
  · intro hsub x hxI
    have hx_mem : x ∈ w₁ ++ sfx := List.mem_toFinset.mp (hsub hxI)
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx_mem
    have hklay : M.G.layer (w₁ ++ sfx)[k] = k + 1 := hw.2 k hk
    have hkle : k + 1 ≤ w₁.length := by
      rw [← hklay]
      exact hIlay (w₁ ++ sfx)[k] hxI
    have hkw : k < w₁.length := by omega
    rw [List.getElem_append_left hkw]
    exact List.mem_toFinset.mpr (List.getElem_mem hkw)
  · intro hsub x hxI
    exact List.mem_toFinset.mpr (List.mem_append_left sfx (List.mem_toFinset.mp (hsub hxI)))

end Lemma10Aux

theorem solution (M : GMDP) (hM : M.WF) (π : GPolicy M) (hπ : IsGPolicy M π) (r : ℕ) :
    Sat7 M r (visitMoment M π) := by
  intro i hi1 hi2 c hc hclay u hulay I hcI hIlay _
  set rem := M.G.H - (i + 1)
  have hH_split1 : M.G.H = i + (1 + rem) := by omega
  have hH_split0 : M.G.H = i + (M.G.H - i) := by omega
  have h_rhs : visitMoment M π I =
      Lemma10Aux.extSum M π i [] (fun w₁ => liftInd w₁.toFinset I) := by
    rw [Lemma10Aux.visitMoment_eq_extSum]
    conv_lhs => rw [hH_split0]
    rw [Lemma10Aux.extSum_add]
    refine Lemma10Aux.extSum_congr_good M hM π hπ i [] (Lemma10Aux.goodPrefix_nil M)
      (by simp; omega) ?_
    intro w₁ hw₁len hw₁
    simp only [List.nil_append] at hw₁ ⊢
    have hcongr : Lemma10Aux.extSum M π (M.G.H - i) w₁ (fun P => liftInd P.toFinset I) =
        Lemma10Aux.extSum M π (M.G.H - i) w₁ (fun _ => 1 * liftInd w₁.toFinset I) := by
      refine Lemma10Aux.extSum_congr_good M hM π hπ (M.G.H - i) w₁ hw₁ (by omega) ?_
      intro sfx _ hgood
      have hiff := Lemma10Aux.subset_append_iff_of_layer_le M w₁ sfx hgood I
        (by simpa [hw₁len] using hIlay)
      simp only [liftInd, hiff, one_mul]
    rw [hcongr, Lemma10Aux.extSum_mul_const,
      Lemma10Aux.extSum_const_one M hM π hπ (M.G.H - i) w₁ hw₁ (by omega), one_mul]
  have h_lhs : visitMoment M π (insert u I) =
      Lemma10Aux.extSum M π i [] (fun w₁ => liftInd w₁.toFinset I * M.p c u) := by
    rw [Lemma10Aux.visitMoment_eq_extSum]
    conv_lhs => rw [hH_split1]
    rw [Lemma10Aux.extSum_add]
    refine Lemma10Aux.extSum_congr_good M hM π hπ i [] (Lemma10Aux.goodPrefix_nil M)
      (by simp; omega) ?_
    intro w₁ hw₁len hw₁
    simp only [List.nil_append] at hw₁ ⊢
    have h1 : 1 + rem = rem + 1 := Nat.add_comm 1 rem
    rw [h1]
    simp only [Lemma10Aux.extSum]
    by_cases hIw : I ⊆ w₁.toFinset
    · have hc_mem : c ∈ w₁ := List.mem_toFinset.mp (hIw hcI)
      obtain ⟨k, hk, hwk⟩ := List.getElem_of_mem hc_mem
      have hk_lay : M.G.layer w₁[k] = k + 1 := hw₁.2 k hk
      rw [hwk, hclay] at hk_lay
      have hk_eq : k = w₁.length - 1 := by omega
      have hlast : w₁.getLast? = some c := by
        rw [List.getLast?_eq_getElem?, ← hk_eq, List.getElem?_eq_getElem hk, hwk]
      have hsw : ∀ v, Lemma10Aux.stepWeight M π w₁ v = M.p c v := by
        intro v
        simp [Lemma10Aux.stepWeight, hlast, hc]
      simp_rw [hsw]
      have hvanish : ∀ v : Fin M.G.N, v ≠ u →
          M.p c v * Lemma10Aux.extSum M π rem (w₁ ++ [v])
            (fun P => liftInd P.toFinset (insert u I)) = 0 := by
        intro v hvu
        by_cases hpv : M.p c v = 0
        · simp [hpv]
        · have hstep_nz : Lemma10Aux.stepWeight M π w₁ v ≠ 0 := by rwa [hsw]
          have hw₁v := Lemma10Aux.goodPrefix_snoc M hM π hπ w₁ hw₁ (by omega) v hstep_nz
          have hzero : Lemma10Aux.extSum M π rem (w₁ ++ [v])
              (fun P => liftInd P.toFinset (insert u I)) =
              Lemma10Aux.extSum M π rem (w₁ ++ [v]) (fun _ => 0) := by
            refine Lemma10Aux.extSum_congr_good M hM π hπ rem (w₁ ++ [v]) hw₁v
              (by simp; omega) ?_
            intro sfx _ hgood
            have hu_not : u ∉ ((w₁ ++ [v]) ++ sfx).toFinset := by
              intro hu_mem
              have hu_list : u ∈ (w₁ ++ [v]) ++ sfx := List.mem_toFinset.mp hu_mem
              obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hu_list
              have hlay_idx := hgood.2 idx hidx
              rw [hget, hulay] at hlay_idx
              have hidx_eq : idx = w₁.length := by omega
              subst hidx_eq
              have hget_v : ((w₁ ++ [v]) ++ sfx)[w₁.length] = v := by
                have hlt1 : w₁.length < (w₁ ++ [v]).length := by simp
                rw [List.getElem_append_left hlt1]
                simp
              rw [hget_v] at hget
              exact hvu hget
            have hnot_sub : ¬ (insert u I ⊆ ((w₁ ++ [v]) ++ sfx).toFinset) := by
              intro hsub
              exact hu_not (hsub (Finset.mem_insert_self u I))
            simp only [liftInd, hnot_sub, ↓reduceIte]
          rw [hzero, Lemma10Aux.extSum_zero_fn, mul_zero]
      rw [Finset.sum_eq_single u (fun v _ hvu => hvanish v hvu)
        (fun hu_univ => (hu_univ (Finset.mem_univ u)).elim)]
      simp only [liftInd, hIw, ↓reduceIte, one_mul]
      by_cases hpu : M.p c u = 0
      · simp [hpu]
      · have hstep_nz : Lemma10Aux.stepWeight M π w₁ u ≠ 0 := by rwa [hsw]
        have hw₁u := Lemma10Aux.goodPrefix_snoc M hM π hπ w₁ hw₁ (by omega) u hstep_nz
        have hone : Lemma10Aux.extSum M π rem (w₁ ++ [u])
            (fun P => if insert u I ⊆ P.toFinset then (1 : ℝ) else 0) =
            Lemma10Aux.extSum M π rem (w₁ ++ [u]) (fun _ => 1) := by
          refine Lemma10Aux.extSum_congr_good M hM π hπ rem (w₁ ++ [u]) hw₁u
            (by simp; omega) ?_
          intro sfx _ _
          have hsub_all : insert u I ⊆ ((w₁ ++ [u]) ++ sfx).toFinset := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hxI
            · simp
            · exact List.mem_toFinset.mpr
                (List.mem_append_left sfx (List.mem_append_left [u]
                  (List.mem_toFinset.mp (hIw hxI))))
          exact if_pos hsub_all
        rw [hone, Lemma10Aux.extSum_const_one M hM π hπ rem (w₁ ++ [u]) hw₁u (by simp; omega),
          mul_one]
    · simp only [liftInd, hIw, ↓reduceIte, zero_mul]
      refine Finset.sum_eq_zero fun v _ => ?_
      by_cases hsv : Lemma10Aux.stepWeight M π w₁ v = 0
      · simp [hsv]
      · have hw₁v := Lemma10Aux.goodPrefix_snoc M hM π hπ w₁ hw₁ (by omega) v hsv
        have hzero : Lemma10Aux.extSum M π rem (w₁ ++ [v])
            (fun P => if insert u I ⊆ P.toFinset then (1 : ℝ) else 0) =
            Lemma10Aux.extSum M π rem (w₁ ++ [v]) (fun _ => 0) := by
          refine Lemma10Aux.extSum_congr_good M hM π hπ rem (w₁ ++ [v]) hw₁v
            (by simp; omega) ?_
          intro sfx _ hgood
          have hnot_sub : ¬ (insert u I ⊆ ((w₁ ++ [v]) ++ sfx).toFinset) := by
            intro hsub
            have hI_sub : I ⊆ (w₁ ++ ([v] ++ sfx)).toFinset := by
              intro x hxI
              have := hsub (Finset.mem_insert_of_mem hxI)
              simpa [List.append_assoc] using this
            have hgood' : Lemma10Aux.GoodPrefix M (w₁ ++ ([v] ++ sfx)) := by
              simpa [List.append_assoc] using hgood
            have hIw' := (Lemma10Aux.subset_append_iff_of_layer_le M w₁ ([v] ++ sfx) hgood' I
              (by simpa [hw₁len] using hIlay)).mp hI_sub
            exact hIw hIw'
          exact if_neg hnot_sub
        rw [hzero, Lemma10Aux.extSum_zero_fn, mul_zero]
  rw [h_lhs, h_rhs, ← Lemma10Aux.extSum_mul_const]
