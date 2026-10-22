-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P03.ot_receiverSecurity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:33:27.435767+00:00
-- url     : https://prove2.me/submissions/8d6d6ea0-74bb-4527-a464-b82d7712eaac

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

open QAlgorithms
open scoped Matrix

lemma g73a_unit (e x y : Bool) :
    ∑ b : Bool, conj (bb84Basis e x b) * bb84Basis e y b = if x = y then 1 else 0 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  cases e <;> cases x <;> cases y <;>
    simp [bb84Basis, hadamard, Fintype.sum_bool, Matrix.one_apply, ← two_mul] <;>
    field_simp <;> simp [h2]

def g73a_flip {n : ℕ} (j : Fin n) (z : Qubits n) : Qubits n := Function.update z j (!z j)

lemma g73a_flip_flip {n : ℕ} (j : Fin n) (z : Qubits n) : g73a_flip j (g73a_flip j z) = z := by
  funext i; by_cases h : i = j
  · subst h; simp [g73a_flip]
  · simp [g73a_flip, Function.update_of_ne h]

def g73a_flipEquiv {n : ℕ} (j : Fin n) : Qubits n ≃ Qubits n :=
  ⟨g73a_flip j, g73a_flip j, g73a_flip_flip j, g73a_flip_flip j⟩

lemma g73a_flip_sum_aux {n : ℕ} (F : Qubits n → ℂ) (g : Fin n → Bool → ℂ) (j : Fin n)
    (hF : ∀ z, F (g73a_flip j z) = F z) :
    2 * ∑ z, F z * ∏ i, g i (z i) =
      ∑ z, F z * (g j false + g j true) * ∏ i ∈ Finset.univ.erase j, g i (z i) := by
  have hR : ∀ z, ∏ i ∈ Finset.univ.erase j, g i (g73a_flip j z i) =
      ∏ i ∈ Finset.univ.erase j, g i (z i) := by
    intro z; apply Finset.prod_congr rfl; intro i hi
    rw [g73a_flip, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have hsplit : ∀ z : Qubits n, ∏ i, g i (z i) = g j (z j) * ∏ i ∈ Finset.univ.erase j, g i (z i) :=
    fun z => (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
  have hperm : ∑ z, F z * ∏ i, g i (z i) = ∑ z, F z * (g j (!z j) * ∏ i ∈ Finset.univ.erase j, g i (z i)) := by
    rw [← Equiv.sum_comp (g73a_flipEquiv j)]
    apply Finset.sum_congr rfl; intro z _
    simp only [g73a_flipEquiv, Equiv.coe_fn_mk]
    rw [hF, hsplit, hR]; simp [g73a_flip]
  rw [two_mul]
  conv_lhs => arg 1; rw [Finset.sum_congr rfl (fun z _ => by rw [hsplit z])]
  rw [hperm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro z _
  cases z j <;> simp <;> ring

lemma g73a_flip_sum {n : ℕ} (F : Qubits n → ℂ) (h h' : Fin n → Bool → ℂ) (j : Fin n)
    (hF : ∀ z, F (g73a_flip j z) = F z) (hh : ∀ i, i ≠ j → h i = h' i)
    (hs : h j false + h j true = h' j false + h' j true) :
    ∑ z, F z * ∏ i, h i (z i) = ∑ z, F z * ∏ i, h' i (z i) := by
  have a := g73a_flip_sum_aux F h j hF
  have b := g73a_flip_sum_aux F h' j hF
  have : ∀ z : Qubits n, ∏ i ∈ Finset.univ.erase j, h i (z i) = ∏ i ∈ Finset.univ.erase j, h' i (z i) := by
    intro z; apply Finset.prod_congr rfl; intro i hi; rw [hh i (Finset.ne_of_mem_erase hi)]
  simp_rw [this, hs] at a
  have := a.trans b.symm
  exact mul_left_cancel₀ two_ne_zero this

lemma g73a_pad_congr {n : ℕ} (x y theta : Qubits n) (b : Bool)
    (h : ∀ i, theta i = b → y i = x i) :
    paddedRestriction y theta b = paddedRestriction x theta b := by
  funext j
  unfold paddedRestriction
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_filter] at hi
  exact h i (by simpa using hi.2)

def g73a_g {n : ℕ} (β a b : Qubits n) : Fin n → Bool → ℂ :=
  fun i bit => conj (bb84Basis (β i) (a i) bit) * bb84Basis (β i) (b i) bit

lemma g73a_change {n : ℕ} (F : Qubits n → ℂ) (θ : Qubits n) (c : Bool)
    (hF : ∀ j, θ j ≠ c → ∀ z, F (g73a_flip j z) = F z) (a b : Qubits n) :
    ∑ z, F z * ∏ i, g73a_g θ a b i (z i) = ∑ z, F z * ∏ i, g73a_g (fun _ => c) a b i (z i) := by
  have key : ∀ T : Finset (Fin n), (∀ j ∈ T, θ j ≠ c) →
      ∑ z, F z * ∏ i, g73a_g θ a b i (z i) =
        ∑ z, F z * ∏ i, g73a_g (fun i => if i ∈ T then c else θ i) a b i (z i) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | insert j T hj ih =>
      intro hT
      rw [ih (fun k hk => hT k (Finset.mem_insert_of_mem hk))]
      apply g73a_flip_sum F _ _ j (hF j (hT j (Finset.mem_insert_self j T)))
      · intro i hi
        funext bit
        simp only [g73a_g, Finset.mem_insert, hi, false_or]
      · have e : ∀ β : Qubits n, g73a_g β a b j false + g73a_g β a b j true =
            if a j = b j then 1 else 0 := by
          intro β
          rw [← g73a_unit (β j) (a j) (b j), Fintype.sum_bool, add_comm]; rfl
        rw [e, e]
  have := key (Finset.univ.filter (fun i => θ i ≠ c)) (fun j hj => (Finset.mem_filter.mp hj).2)
  rw [this]
  congr 1; funext z; congr 1; apply Finset.prod_congr rfl; intro i _
  congr 1
  funext i'
  by_cases h : θ i' = c <;> simp [h]

def g73a_res {n : ℕ} {M : Type*} (ρ : Matrix (Qubits n × M) (Qubits n × M) ℂ) (β z : Qubits n) :
    Matrix M M ℂ :=
  fun m m' => ∑ a : Qubits n, ∑ b : Qubits n,
    conj (tensorBasisColumn bb84Basis β z a) * ρ (a,m) (b,m') * tensorBasisColumn bb84Basis β z b

lemma g73a_vv {n : ℕ} (β z a b : Qubits n) :
    conj (tensorBasisColumn bb84Basis β z a) * tensorBasisColumn bb84Basis β z b =
      ∏ i, g73a_g β a b i (z i) := by
  simp [tensorBasisColumn, map_prod, Finset.prod_mul_distrib, g73a_g]

lemma g73a_res_eq {n : ℕ} {M : Type*} (ρ : Matrix (Qubits n × M) (Qubits n × M) ℂ)
    (F : Qubits n → ℂ) (θ : Qubits n) (c : Bool)
    (hF : ∀ j, θ j ≠ c → ∀ z, F (g73a_flip j z) = F z) :
    ∑ z, F z • g73a_res ρ θ z = ∑ z, F z • g73a_res ρ (fun _ => c) z := by
  ext m m'
  simp only [Matrix.sum_apply, Matrix.smul_apply, g73a_res, smul_eq_mul]
  have e : ∀ β : Qubits n, ∑ z, F z * ∑ a, ∑ b,
      conj (tensorBasisColumn bb84Basis β z a) * ρ (a,m) (b,m') * tensorBasisColumn bb84Basis β z b
      = ∑ a, ∑ b, ρ (a,m) (b,m') * ∑ z, F z * ∏ i, g73a_g β a b i (z i) := by
    intro β
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro z _
    rw [← g73a_vv]; ring
  rw [e, e]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  rw [g73a_change F θ c hF a b]

lemma g73a_res_psd {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    {ρ : Matrix (Qubits n × M) (Qubits n × M) ℂ} (hρ : ρ.PosSemidef) (β z : Qubits n) :
    (g73a_res ρ β z).PosSemidef := by
  set v : Qubits n → ℂ := fun a => tensorBasisColumn bb84Basis β z a with hv
  set L : Matrix (Qubits n × M) M ℂ := fun p m => if p.2 = m then v p.1 else 0 with hL
  have e : g73a_res ρ β z = Lᴴ * ρ * L := by
    ext m m'
    unfold g73a_res
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b _
    simp only [hL, Finset.sum_mul]
    rw [Finset.sum_eq_single m']
    · rw [Finset.sum_comm, Finset.sum_eq_single m]
      · simp [hv]
      · intro m1 _ hm1; apply Finset.sum_eq_zero; intro a _; simp [hm1]
      · simp
    · intro m2 _ hm2; apply Finset.sum_eq_zero; intro a _
      apply Finset.sum_eq_zero; intro m1 _; simp [hm2]
    · simp
  rw [e]; exact hρ.conjTranspose_mul_mul_same L

lemma g73a_chan_sum {ι κ Z : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Fintype Z]
    {Φ : Superop ι κ} (hΦ : IsChannel Φ) (F : Z → ℂ) (R : Z → Matrix ι ι ℂ) :
    Φ (∑ z, F z • R z) = ∑ z, F z • Φ (R z) := by
  obtain ⟨m, E, -, hE⟩ := hΦ
  simp only [hE, krausApply, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum]
  exact Finset.sum_comm

lemma g73a_chan_psd {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {Φ : Superop ι κ} (hΦ : IsChannel Φ) {R : Matrix ι ι ℂ} (hR : R.PosSemidef) :
    (Φ R).PosSemidef := by
  obtain ⟨m, E, -, hE⟩ := hΦ
  rw [hE, krausApply]
  have : ∀ s : Finset (Fin m), (∑ j ∈ s, E j * R * (E j)ᴴ).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using Matrix.PosSemidef.zero
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact (hR.mul_mul_conjTranspose_same _).add ih
  exact this _

lemma g73a_sum_ind_psd {ι Z : Type*} [Fintype ι] [Fintype Z] (P : Z → Prop) [DecidablePred P]
    {R : Z → Matrix ι ι ℂ} (hR : ∀ z, (R z).PosSemidef) :
    (∑ z, (if P z then (1:ℂ) else 0) • R z).PosSemidef := by
  have : ∀ s : Finset Z, (∑ z ∈ s, (if P z then (1:ℂ) else 0) • R z).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using Matrix.PosSemidef.zero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine Matrix.PosSemidef.add ?_ ih
      split_ifs
      · simpa using hR a
      · simpa using Matrix.PosSemidef.zero
  exact this _

lemma g73a_blk_sum {T M E Z : Type*} [Fintype M] [DecidableEq M] [Fintype E] [Fintype T] [Fintype Z]
    {Φ : Superop M (T × E)} (hΦ : IsChannel Φ) (t : T) (F : Z → ℂ) (R : Z → Matrix M M ℂ) :
    (fun a b => Φ (∑ z, F z • R z) (t,a) (t,b)) = ∑ z, F z • (fun a b => Φ (R z) (t,a) (t,b) : Matrix E E ℂ) := by
  rw [g73a_chan_sum hΦ]
  ext a b
  simp [Matrix.sum_apply, Matrix.smul_apply]

lemma g73a_regroup {Z Sx V : Type*} [Fintype Z] [Fintype Sx] {dS : DecidableEq Sx}
    [AddCommGroup V] [Module ℂ V] (P : Sx → Prop) {dP : DecidablePred P} (Sf : Z → Sx)
    (Q : Z → Prop) {dQ : DecidablePred Q} (hPQ : ∀ z, P (Sf z) ↔ Q z) (X : Z → V) :
    (∑ s, if P s then ∑ z, (if Sf z = s then (1:ℂ) else 0) • X z else 0) =
      ∑ z, (if Q z then (1:ℂ) else 0) • X z := by
  calc (∑ s, if P s then ∑ z, (if Sf z = s then (1:ℂ) else 0) • X z else 0)
      = ∑ s, ∑ z, ((if P s then (1:ℂ) else 0) * (if Sf z = s then (1:ℂ) else 0)) • X z := by
        apply Finset.sum_congr rfl; intro s _
        split_ifs <;> simp
    _ = ∑ z, (∑ s, (if P s then (1:ℂ) else 0) * (if Sf z = s then (1:ℂ) else 0)) • X z := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro z _
        rw [Finset.sum_smul]
    _ = _ := by
        apply Finset.sum_congr rfl; intro z _
        congr 1
        simp only [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_univ, if_true]
        by_cases h : Q z
        · rw [if_pos ((hPQ z).mpr h), if_pos h]
        · rw [if_neg (fun h' => h ((hPQ z).mp h')), if_neg h]

theorem g73a_recvSec (n ell : ℕ) : OTPerfectReceiverSecure n ell := by
  intro M E _ _ _ _ _ _ A pc
  obtain ⟨S, hS⟩ : ∃ S : SenderAnnouncement n ell → Qubits n → Qubits ell × Qubits ell,
    S = fun t z => (t.2.1 (paddedRestriction z t.1 false), t.2.2 (paddedRestriction z t.1 true)) :=
    ⟨_, rfl⟩
  obtain ⟨blk, hblk⟩ : ∃ blk : SenderAnnouncement n ell → Matrix M M ℂ → Matrix E E ℂ,
    blk = fun t R => fun a b => A.announce R (t,a) (t,b) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : (Qubits ell × Qubits ell) → SenderAnnouncement n ell → Matrix E E ℂ,
    K = fun s t => blk t (∑ z, (if S t z = s then (1:ℂ) else 0) • g73a_res A.initial t.1 z) :=
    ⟨_, rfl⟩
  have hK_psd : ∀ s t, (K s t).PosSemidef := by
    intro s t
    rw [hK, hblk]
    have h1 := g73a_chan_psd A.physical (g73a_sum_ind_psd (fun z => S t z = s)
      (fun z => g73a_res_psd A.state.1 t.1 z))
    exact h1.submatrix (fun a => (t,a))
  have hpc : ((pc false).toReal : ℂ) + ((pc true).toReal : ℂ) = 1 := by
    have h1 : pc false + pc true = 1 := by
      have := PMF.tsum_coe pc; rw [tsum_fintype, Fintype.sum_bool] at this; rw [add_comm]; exact this
    have h2 : (pc false).toReal + (pc true).toReal = 1 := by
      rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _), h1]; simp
    exact_mod_cast h2
  have hSc : ∀ t z (c : Bool), (if c then (S t z).2 else (S t z).1) = receiverOutput t c z := by
    intro t z c; rw [hS]; cases c <;> rfl
  refine ⟨fun c y s t => (((pc c).toReal : ℝ) : ℂ) •
    (if y = (if c then s.2 else s.1) then K s t else 0), ?_, ?_, ?_, ?_⟩
  · intro c y s t
    beta_reduce
    by_cases h : y = (if c then s.2 else s.1)
    · rw [if_pos h]; exact (hK_psd s t).smul (Complex.zero_le_real.mpr ENNReal.toReal_nonneg)
    · rw [if_neg h, smul_zero]; exact Matrix.PosSemidef.zero
  · intro c y t
    unfold otReceiverBlocks
    beta_reduce
    rw [← Finset.smul_sum]
    congr 1
    have hK' : ∀ s, K s t = ∑ z, (if S t z = s then (1:ℂ) else 0) •
        (fun a b => A.announce (g73a_res A.initial t.1 z) (t,a) (t,b) : Matrix E E ℂ) := by
      intro s; rw [hK, hblk]; beta_reduce; exact g73a_blk_sum A.physical t _ _
    have hR : (∑ yy : Qubits n, if receiverOutput t c yy = y then
        (fun a b => A.announce (receiverResidual A.initial c yy) (t, a) (t, b)) else 0) =
        (fun a b => A.announce (∑ z, (if receiverOutput t c z = y then (1:ℂ) else 0) •
          g73a_res A.initial (fun _ => c) z) (t,a) (t,b)) := by
      rw [g73a_blk_sum A.physical]
      apply Finset.sum_congr rfl; intro z _
      split_ifs
      · rw [one_smul]; rfl
      · rw [zero_smul]
    rw [hR]
    rw [← g73a_res_eq A.initial _ t.1 c]
    · rw [g73a_blk_sum A.physical]
      simp_rw [hK']
      exact g73a_regroup (V := Matrix E E ℂ) (fun s => y = (if c then s.2 else s.1)) (S t)
        (fun z => receiverOutput t c z = y)
        (fun z => by rw [hSc t z c]; exact eq_comm) _
    · intro j hj z
      have : receiverOutput t c (g73a_flip j z) = receiverOutput t c z := by
        unfold receiverOutput
        rw [g73a_pad_congr z (g73a_flip j z) t.1 c]
        intro i hi
        have : i ≠ j := by rintro rfl; exact hj hi
        simp [g73a_flip, Function.update_of_ne this]
      rw [this]
  · intro c y s t h
    beta_reduce
    rw [if_neg h, smul_zero]
  · intro c s t
    beta_reduce
    have hsum : ∀ c' : Bool, (∑ y : Qubits ell, (((pc c').toReal : ℝ) : ℂ) •
        (if y = (if c' then s.2 else s.1) then K s t else 0)) = (((pc c').toReal : ℝ) : ℂ) • K s t := by
      intro c'
      rw [← Finset.smul_sum, Finset.sum_ite_eq']
      simp
    rw [hsum c]
    simp_rw [hsum]
    rw [Fintype.sum_bool, ← add_smul, add_comm, hpc, one_smul]


lemma g73a_col (e x y : Bool) :
    ∑ b : Bool, conj (bb84Basis e b y) * bb84Basis e b x = if y = x then 1 else 0 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  cases e <;> cases x <;> cases y <;>
    simp [bb84Basis, hadamard, Matrix.one_apply, ← two_mul] <;>
    field_simp <;> simp [h2]

lemma g73a_pad_congr' {n : ℕ} (x y theta : Qubits n) (b : Bool)
    (h : ∀ i, theta i = b → y i = x i) :
    paddedRestriction y theta b = paddedRestriction x theta b := by
  funext j
  unfold paddedRestriction
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_filter] at hi
  exact h i (by simpa using hi.2)

lemma g73a_honest_zero {n : ℕ} (x θ y : Qubits n) (c : Bool) (i : Fin n) (hi : θ i = c)
    (hne : y i ≠ x i) : honestOutcomeProb x θ c y = 0 := by
  set v := tensorBasisColumn bb84Basis (fun _ => c) y
  set w := tensorBasisColumn bb84Basis θ x
  have hinner : ∑ b, conj (v b) * w b = 0 := by
    have : ∀ b : Qubits n, conj (v b) * w b =
        ∏ k, (conj (bb84Basis c (b k) (y k)) * bb84Basis (θ k) (b k) (x k)) := by
      intro b
      simp [v, w, tensorBasisColumn, map_prod, Finset.prod_mul_distrib]
    simp_rw [this]
    have hps := (Fintype.prod_sum (fun (k : Fin n) (bit : Bool) =>
      conj (bb84Basis c bit (y k)) * bb84Basis (θ k) bit (x k))).symm
    refine hps.trans ?_
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hi, g73a_col c (x i) (y i), if_neg hne]
  unfold honestOutcomeProb effectProb
  have : ((pureDensity v) * (pureDensity w)).trace =
      (∑ a, v a * conj (w a)) * ∑ b, conj (v b) * w b := by
    rw [Finset.sum_mul_sum]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring
  rw [this, hinner, mul_zero, Complex.zero_re]

theorem g73a_honestOT (n ell : ℕ) : HonestOTCorrect n ell := by
  intro f0 f1 c
  apply Finset.sum_eq_zero; intro x _
  apply Finset.sum_eq_zero; intro θ _
  apply Finset.sum_eq_zero; intro y _
  by_cases h : ∀ i, θ i = c → y i = x i
  · rw [g73a_pad_congr' x y θ c h, if_pos rfl, mul_zero]
  · push_neg at h
    obtain ⟨i, hi, hne⟩ := h
    rw [g73a_honest_zero x θ y c i hi hne]; ring

/-- Proposition 4.5, pp.10-11: the concrete Figure 1 protocol is perfectly
receiver-secure, including the full extraction, for every input distribution.
Honest correctness is also verified for the explicit protocol computation. -/
theorem solution (n ell : ℕ) :
    HonestOTCorrect n ell ∧ OTPerfectReceiverSecure n ell := ⟨g73a_honestOT n ell, g73a_recvSec n ell⟩


end
